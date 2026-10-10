import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.OuterRealization
import OAI.Geometry.Relativity.CKS.MetricSymbols
import OAI.Geometry.Relativity.CKS.TailTensor

namespace OAI

namespace CKSSpatialManifold

end CKSSpatialManifold

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

def constructedEnergy (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : Point) : ℝ :=
  (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x).energy
    (constructedTensorJet f₀ m R x)

theorem constructed_energy_tail_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ C : ℝ, 12 ≤ R₀ ∧ 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
      2*R^2 < x 0 → Real.sin (x 1) ≠ 0 →
      |constructedEnergy f₀ m R x| ≤ C/((x 0)^3*Real.sqrt (x 0)) := by
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  refine ⟨max 12 (4*M),2+4*M*B+12*B^2,le_max_left _ _,by positivity,?_⟩
  intro R hR x hr hs
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRM : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := lt_trans (by positivity : 0 < 2*R^2) hr
  have hr3 : 3*R ≤ x 0 := by nlinarith
  have hrM : 4*M ≤ x 0 := by linarith
  have hv0 := bendingV_tail hRp hr.le
  have hvp := bendingV_tail_deriv hRp hr
  have hβ0 := bendingBeta_tail hR12 hr.le
  have hζ1 := bendingZeta_tail hR12 hr.le
  obtain ⟨hm,hΔ,hg,ht⟩ := hbound R hR12 x hr3 hs
  have hpos : 0 < radicand (outerMass f₀ m R) (bendingV R) x := by
    have hq : 2*outerMass f₀ m R x/x 0 ≤ 1/2 :=
      (div_le_iff₀ hrp).mpr (by linarith [(le_abs_self _).trans hm])
    dsimp [radicand,radial]
    nlinarith [sq_nonneg (bendingV R (x 0))]
  have hF : ContDiffAt ℝ 2 (outerMass f₀ m R) x :=
    ((outerMass_smooth f₀ hf₀ m hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv : ContDiffAt ℝ 2 (bendingV R) (x 0) :=
    ((bendingV_smooth hRp).contDiffAt (isOpen_Ioi.mem_nhds hrp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ha := ((outerA_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).differentiableAt (by simp)
  have hb := ((outerPhi_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).differentiableAt (by simp)
  have he := smooth_energy_residual hF hv ((bendingBeta_smooth R).differentiable (by simp) _) ha hb
    hrp.ne' hs hpos (outerMass_heat f₀ hf₀ m hRp hr3 hs)
  rw [hv0,hvp,hβ0,hζ1] at he
  simp only [zero_div,sub_zero] at he
  change |(metricJet _ x).energy _| ≤ _
  rw [constructedTensorJet,he]
  apply vanishing_tail_energy_bound (by linarith) (lapse_pos hpos) hM hB hm hrM _ hΔ hg
  simpa only [A,radial,hv0] using lapse_sq hpos

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma actual_inverse_derivative {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (v : PhysicalPoint) :
    (fun i j => D v (fun y => (G y)⁻¹ i j) x) =
      -(G x)⁻¹ * (show AmbientMat from fun i j => D v (fun y => G y i j) x) * (G x)⁻¹ := by
  let dG : AmbientMat := fun i j => D v (fun y => G y i j) x
  let dI : AmbientMat := fun i j => D v (fun y => (G y)⁻¹ i j) x
  have hc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by simp)
  have hi (i j) : DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x :=
    (matrix_inv_component_contDiffAt hg h0 i j).differentiableAt (by simp)
  have hz : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    (matrix_det_contDiffAt hg).continuousAt.eventually_ne h0
  have hD : dG * (G x)⁻¹ + G x * dI = 0 := by
    ext i j
    have hd : D v (fun y => (G y * (G y)⁻¹) i j) x = 0 := by
      calc
        _ = D v (fun _ => (1 : AmbientMat) i j) x := by
          apply D_congr
          filter_upwards [hz] with y hy
          rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)]
        _ = 0 := D_const _ _ _
    simp only [Matrix.mul_apply] at hd
    rw [D_sum3 v (fun k y => G y i k * (G y)⁻¹ k j)
      (fun k => (hc i k).fun_mul (hi k j))] at hd
    simp only [D_mul _ (hc i _) (hi _ j)] at hd
    change (∑ k, dG i k * (G x)⁻¹ k j) + (∑ k, G x i k * dI k j) = 0
    simpa only [dG, dI, Finset.sum_add_distrib, add_comm, mul_comm] using hd
  have hIG : (G x)⁻¹ * G x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h0)
  have hD' : G x * dI = -(dG * (G x)⁻¹) := (eq_neg_iff_add_eq_zero).2 (by
    simpa only [add_comm] using hD)
  change dI = -(G x)⁻¹ * dG * (G x)⁻¹
  calc
    dI = ((G x)⁻¹ * G x) * dI := by rw [hIG, one_mul]
    _ = (G x)⁻¹ * (G x * dI) := mul_assoc _ _ _
    _ = -(G x)⁻¹ * dG * (G x)⁻¹ := by rw [hD']; simp only [mul_neg, neg_mul, mul_assoc]

lemma physicalMetricJet_dInv {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (a i j : Fin 3) :
    D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
      (physicalMetricJet G x).dInv a i j := by
  have h := congrFun (congrFun (actual_inverse_derivative hg h0
    (CKSRealizedRound.basis a)) i) j
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_apply] at h
  change D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
    -(∑ c, (∑ b, (G x)⁻¹ i b * D (CKSRealizedRound.basis a)
      (fun y => G y b c) x) * (G x)⁻¹ c j) at h
  rw [h]
  simp only [CKSRound.MetricJet.dInv, physicalMetricJet, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = coordinateChristoffel G x i j a := by
  simp only [CKSRound.MetricJet.gamma, physicalMetricJet, coordinateChristoffel,
    lowerKoszul, actualMetricFirstJet, Finset.sum_div]
  apply Finset.sum_congr rfl; intro l _
  rw [hermitian_real_symmetry hs.inv a l]
  ring

lemma physicalMetricJet_dGamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    D (CKSRealizedRound.basis s) (fun y => coordinateChristoffel G y i j a) x =
      (physicalMetricJet G x).dGamma s a i j := by
  have hc (b c) : ContDiffAt ℝ ∞ (fun y => G y b c) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg b) c
  have hd (b c d) : DifferentiableAt ℝ
      (fun y => D (CKSRealizedRound.basis b) (fun z => G z c d) y) x :=
    (contDiffAt_D (hc c d) (m := ∞) (by simp) _).differentiableAt (by simp)
  have hi (b c) : DifferentiableAt ℝ (fun y => (G y)⁻¹ b c) x :=
    (matrix_inv_component_contDiffAt hg h0 b c).differentiableAt (by simp)
  have ht (l) := ((hd i j l).fun_add (hd j i l)).fun_sub (hd l i j)
  have hm (l) := (hi a l).fun_mul (ht l)
  calc
    _ = D (CKSRealizedRound.basis s) (fun y => (physicalMetricJet G y).gamma a i j) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact (physicalMetricJet_gamma hy a i j).symm
    _ = _ := by
      unfold CKSRound.MetricJet.gamma
      change D (CKSRealizedRound.basis s) (fun y =>
        (∑ l, (G y)⁻¹ a l * (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
          D (CKSRealizedRound.basis j) (fun z => G z i l) y -
          D (CKSRealizedRound.basis l) (fun z => G z i j) y)) / 2) x = _
      rw [physical_D_div_const _ (DifferentiableAt.fun_sum (fun l _ => hm l)),
        D_sum3 _ _ hm]
      unfold CKSRound.MetricJet.dGamma
      congr 1
      apply Finset.sum_congr rfl; intro l _
      rw [D_mul _ (hi a l) (ht l), D_sub _ ((hd i j l).fun_add (hd j i l)) (hd l i j),
        D_add _ (hd i j l) (hd j i l), physicalMetricJet_dInv hg h0]
      simp only [physicalMetricJet]
      ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 3
abbrev P := PhysicalPoint
abbrev Vect := PhysicalPoint
abbrev Symbols := A → A → A → ℝ

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D v f x

lemma delta_expansion (v : Vect) (f : P → ℝ) (x : P) :
    delta v f x = ∑ i : A, v i * D (CKSRealizedRound.basis i) f x :=
  D_direction_expansion v x f

lemma delta_mul (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y * g y) x = f x * delta v g x + g x * delta v f x :=
  D_mul _ hf hg

lemma delta_add (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y + g y) x = delta v f x + delta v g x :=
  D_add _ hf hg

lemma delta_sum (v : Vect) {x : P} (f : A → P → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    delta v (fun y => ∑ i, f i y) x = ∑ i, delta v (f i) x :=
  D_sum3 _ f hf

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

lemma delta_moving (v : Vect) {W : P → Vect} {f : P → ℝ} {x : P}
    (hW : DifferentiableAt ℝ W x) (hf : ContDiffAt ℝ 2 f x) :
    delta v (fun y => delta (W y) f y) x =
      ∑ i : A, (W x i * delta v (D (CKSRealizedRound.basis i) f) x +
        D (CKSRealizedRound.basis i) f x * delta v (fun y => W y i) x) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hfi (i : A) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i) f) x :=
    (contDiffAt_D hf (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [delta_expansion (W _)]
  rw [delta_sum _ (fun i y => W y i * D (CKSRealizedRound.basis i) f y)
    (fun i => (hWi i).mul (hfi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact delta_mul _ (hWi i) (hfi i)

lemma delta_commutator {V W : P → Vect} {f : P → ℝ} {x : P}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hf : ContDiffAt ℝ 2 f x) :
    delta (V x) (fun y => delta (W y) f y) x -
      delta (W x) (fun y => delta (V y) f y) x = delta (bracket V W x) f x := by
  rw [delta_moving _ hW hf, delta_moving _ hV hf]
  simp only [delta_expansion, bracket, Fin.sum_univ_three]
  rw [D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 1),
    D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 2),
    D_comm hf (CKSRealizedRound.basis 1) (CKSRealizedRound.basis 2)]
  ring

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j) (fun y => Γ y k i l) x +
    ∑ m : A, (Γ x m j l * Γ x k i m - Γ x m i l * Γ x k j m)

lemma delta_nabla (v : Vect) {Γ : P → Symbols} {W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hW : DifferentiableAt ℝ W x)
    (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    delta v (fun y => nabla Γ (W y) Z y k) x =
      delta v (fun y => delta (W y) (fun z => Z z k) y) x +
      ∑ i : A, ∑ j : A,
        (W x i * Z x j * delta v (fun y => Γ y k i j) x +
          Γ x k i j * (W x i * delta v (fun y => Z y j) x +
            Z x j * delta v (fun y => W y i) x)) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hZi (i : A) := contDiffAt_pi.mp hZ i
  have hdZi (i j : A) : DifferentiableAt ℝ
      (D (CKSRealizedRound.basis i) (fun y => Z y j)) x :=
    (contDiffAt_D (hZi j) (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hΓi (a i j : A) : DifferentiableAt ℝ (fun y => Γ y a i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hΓ a) i) j
  have hvZ : DifferentiableAt ℝ (fun y => delta (W y) (fun z => Z z k) y) x := by
    simp only [delta_expansion]
    exact DifferentiableAt.fun_sum fun i _ => (hWi i).mul (hdZi i k)
  have ht (i j : A) : DifferentiableAt ℝ
      (fun y => W y i * Z y j * Γ y k i j) x :=
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))).mul (hΓi k i j)
  have hs (i : A) : DifferentiableAt ℝ (fun y => ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun j _ => ht i j
  have hss : DifferentiableAt ℝ (fun y => ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun i _ => hs i
  change delta v (fun y => delta (W y) (fun z => Z z k) y +
    ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x = _
  rw [delta_add _ hvZ hss, delta_sum _ _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [delta_sum _ _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [delta_mul v (f := fun y => W y i * Z y j) (g := fun y => Γ y k i j)
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))) (hΓi k i j),
    delta_mul v (f := fun y => W y i) (g := fun y => Z y j)
      (hWi i) ((hZi j).differentiableAt (by norm_num))]

theorem curvature_coordinate {Γ : P → Symbols} {V W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    curvature Γ V W Z x k = ∑ i : A, ∑ j : A, ∑ l : A,
      V x i * W x j * Z x l * coordCurvature Γ x k l i j := by
  change (delta (V x) (fun y => nabla Γ (W y) Z y k) x +
      ∑ i : A, ∑ j : A, V x i * nabla Γ (W x) Z x j * Γ x k i j) -
    (delta (W x) (fun y => nabla Γ (V y) Z y k) x +
      ∑ i : A, ∑ j : A, W x i * nabla Γ (V x) Z x j * Γ x k i j) -
    (delta (bracket V W x) (fun y => Z y k) x +
      ∑ i : A, ∑ j : A, bracket V W x i * Z x j * Γ x k i j) = _
  rw [delta_nabla _ hΓ hW hZ, delta_nabla _ hΓ hV hZ]
  have hc := delta_commutator hV hW (contDiffAt_pi.mp hZ k)
  rw [sub_eq_iff_eq_add.mp hc]
  simp only [nabla, coordCurvature, bracket, delta_expansion, Fin.sum_univ_three]
  ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : AmbientMat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

lemma pair_frame_sum (γ : AmbientMat) (E : A → Vect)
    (ho : ∀ a b, pair γ (E a) (E b) = if a = b then 1 else 0)
    (f : A → ℝ) (a : A) :
    pair γ (fun k => ∑ c : A, f c * E c k) (E a) = f a := by
  calc
    _ = ∑ c : A, f c * pair γ (E c) (E a) := by
      simp only [pair, Fin.sum_univ_three]
      ring
    _ = _ := by simp [ho]

lemma inverse_metric_trace {γ : AmbientMat} (hp : γ.PosDef) (k i : A) :
    (∑ m : A, γ k m * γ⁻¹ i m) = if k = i then 1 else 0 := by
  have h : (γ * γ⁻¹) k i = (1 : AmbientMat) k i :=
    congrFun (congrFun (Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) k) i
  simpa only [Matrix.mul_apply, hermitian_real_symmetry hp.isHermitian.inv, Matrix.one_apply] using h

lemma sum_three_rotate (f : A → A → A → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem scalar_frame_contraction {γ : AmbientMat} (hp : γ.PosDef) (E : A → Vect)
    (hg : ∀ i j, (∑ a : A, E a i * E a j) = γ⁻¹ i j)
    (R : A → A → A → A → ℝ) :
    (∑ a : A, ∑ b : A, pair γ
      (fun k => ∑ i : A, ∑ j : A, ∑ l : A, E a i * E b j * E b l * R k l i j)
      (E a)) = ∑ j : A, ∑ l : A, γ⁻¹ j l * ∑ k : A, R k l k j := by
  calc
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        ∑ a : A, ∑ b : A,
          γ k m * E a i * E a m * E b j * E b l * R k l i j := by
      simp only [pair, Finset.mul_sum, Finset.sum_mul]
      conv_lhs =>
        rw [sum_three_rotate]
        arg 2; ext k
        rw [sum_three_rotate]
        arg 2; ext m
        rw [sum_three_rotate]
        arg 2; ext i
        rw [sum_three_rotate]
        arg 2; ext j
        rw [sum_three_rotate]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      calc
        _ = (γ k m * (∑ a : A, E a i * E a m)) *
            (∑ b : A, E b j * E b l) * R k l i j := by
          simp only [Fin.sum_univ_three]
          ring
        _ = _ := by rw [hg, hg]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A, ∑ m : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2; ext i
        rw [Finset.sum_comm]
        arg 2; ext j
        rw [Finset.sum_comm]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (if k = i then 1 else 0) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      rw [← Finset.sum_mul, ← Finset.sum_mul, inverse_metric_trace hp]
    _ = _ := by
      simp only [Fin.sum_univ_three]
      simp
      ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalSymbols (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    CKSAmbientCalculus.Symbols := fun a i j => coordinateChristoffel G x i j a

lemma physicalSymbols_differentiableAt {G : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) :
    DifferentiableAt ℝ (physicalSymbols G) x := by
  apply differentiableAt_pi.mpr; intro a
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  exact (coordinateChristoffel_contDiffAt hg h0 i j a).differentiableAt (by simp)

lemma curvatureVector_coordinate {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (a b c k : Fin 3) :
    curvatureVector G E x a b c k = ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E c x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
  have hz : ContDiffAt ℝ 2 (E c) x := (he c).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change CKSAmbientCalculus.curvature (physicalSymbols G) (E a) (E b) (E c) x k = _
  exact CKSAmbientCalculus.curvature_coordinate (physicalSymbols_differentiableAt hg h0)
    ((he a).differentiableAt (by simp)) ((he b).differentiableAt (by simp))
    hz k

lemma physical_scalar_coordinate_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = ∑ j, ∑ l, (G x)⁻¹ j l * ∑ k,
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j := by
  rw [actualScalar_curvature_trace hg he hp hs ho]
  have hc (a b) : curvatureVector G E x a b b = fun k => ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E b x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
    funext k
    exact curvatureVector_coordinate hg hp.det_pos.ne' he a b b k
  simp only [hc]
  change (∑ a, ∑ b, CKSAmbientCalculus.pair (G x)
    (fun k => ∑ i, ∑ j, ∑ l, E a x i * E b x j * E b x l *
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j) (E a x)) = _
  exact CKSAmbientCalculus.scalar_frame_contraction hp (fun a => E a x)
    (orthonormal_frame_completeness ho.self_of_nhds)
    (CKSAmbientCalculus.coordCurvature (physicalSymbols G) x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = (physicalMetricJet G x).gamma a j i := by
  rw [physicalMetricJet_gamma hs.self_of_nhds, physicalMetricJet_gamma hs.self_of_nhds]
  exact coordinateChristoffel_torsion hs i j a

lemma physicalMetricJet_dGamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    (physicalMetricJet G x).dGamma s a i j = (physicalMetricJet G x).dGamma s a j i := by
  rw [← physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_dGamma hg h0 hs]
  apply D_congr
  filter_upwards [hs.eventually_nhds] with y hy
  exact coordinateChristoffel_torsion hy i j a

lemma physicalMetricJet_ricci {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (l j : Fin 3) :
    (∑ k, CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j) =
      (physicalMetricJet G x).ricci l j := by
  simp only [CKSAmbientCalculus.coordCurvature, physicalSymbols,
    physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_gamma hs.self_of_nhds,
    Finset.sum_add_distrib, CKSRound.MetricJet.ricci]
  apply congrArg₂ (fun u v : ℝ => u + v)
  · apply Finset.sum_congr rfl; intro k _
    rw [physicalMetricJet_dGamma_torsion hg h0 hs k k j l,
      physicalMetricJet_dGamma_torsion hg h0 hs j k k l]
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro m _
    rw [physicalMetricJet_gamma_torsion hs m j l,
      physicalMetricJet_gamma_torsion hs m k l]
    ring

theorem physicalMetricJet_scalar {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = (physicalMetricJet G x).scalar := by
  rw [physical_scalar_coordinate_trace hg he hp hs ho]
  simp only [physicalMetricJet_ricci hg hp.det_pos.ne' hs, CKSRound.MetricJet.scalar]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro j _
  change (G x)⁻¹ j l * _ = (G x)⁻¹ l j * _
  rw [hermitian_real_symmetry hp.isHermitian.inv j l]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_inverse_trace_coordinates {g : AmbientMat} (hs : g.IsHermitian)
    (k : AmbientMat) : (g⁻¹*k).trace = ∑ a, ∑ b, g⁻¹ a b * k a b := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [hermitian_real_symmetry hs.inv b a]

lemma physicalMetricJet_trace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) :
    ((G x)⁻¹*K x).trace = (physicalMetricJet G x).trace (physicalTensorJet K x) :=
  matrix_inverse_trace_coordinates hs (K x)

lemma matrix_tensor_norm_coordinates {g k : AmbientMat} (hs : g.IsHermitian)
    (hk : k.IsHermitian) :
    (g⁻¹*k*g⁻¹*k).trace = ∑ a, ∑ b, ∑ c, ∑ d,
      g⁻¹ a c * g⁻¹ b d * k a b * k c d := by
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  rw [hermitian_real_symmetry hs.inv c a, hermitian_real_symmetry hk d c]
  ring

lemma physicalMetricJet_normSq {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (hk : (K x).IsHermitian) :
    ((G x)⁻¹*K x*(G x)⁻¹*K x).trace =
      (physicalMetricJet G x).normSq (physicalTensorJet K x) :=
  matrix_tensor_norm_coordinates hs hk

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_dTrace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    D (CKSRealizedRound.basis i) (fun y => ((G y)⁻¹*K y).trace) x =
      (physicalMetricJet G x).dTrace (physicalTensorJet K x) i := by
  have hki (a b) : DifferentiableAt ℝ (fun y => K y a b) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).differentiableAt (by simp)
  have hgi (a b) : DifferentiableAt ℝ (fun y => (G y)⁻¹ a b) x :=
    (matrix_inv_component_contDiffAt hg h0 a b).differentiableAt (by simp)
  have ht (a b) := (hgi a b).fun_mul (hki a b)
  calc
    _ = D (CKSRealizedRound.basis i) (fun y => ∑ a, ∑ b, (G y)⁻¹ a b*K y a b) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact matrix_inverse_trace_coordinates hy (K y)
    _ = _ := by
      rw [D_sum3 _ _ (fun a => DifferentiableAt.fun_sum (fun b _ => ht a b))]
      unfold CKSRound.MetricJet.dTrace
      apply Finset.sum_congr rfl; intro a _
      rw [D_sum3 _ _ (ht a)]
      apply Finset.sum_congr rfl; intro b _
      rw [D_mul _ (hgi a b) (hki a b), physicalMetricJet_dInv hg h0]
      simp only [physicalTensorJet, physicalMetricJet]
      ring

lemma physicalMetricJet_tensorCovariant {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hs : (G x).IsHermitian) (a b i : Fin 3) :
    coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (CKSRealizedRound.basis i) x =
        (physicalTensorJet K x).d a b i -
        (∑ c, (physicalMetricJet G x).gamma c a b * (physicalTensorJet K x).val c i) -
        (∑ c, (physicalMetricJet G x).gamma c a i * (physicalTensorJet K x).val b c) := by
  simp only [physicalMetricJet_gamma hs, physicalTensorJet]
  simp [coordinateTensorCovariant, coordinateConnectionVector, metricPair,
    CKSRealizedRound.basis, Pi.single_apply, mul_comm]

theorem physicalMetricJet_momentum {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x)
    (h0 : (G x).det ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    momentumCovector G K x i = (physicalMetricJet G x).momentum (physicalTensorJet K x) i := by
  simp only [momentumCovector, coordinateMomentum,
    matrix_inverse_trace_coordinates hs.self_of_nhds, Matrix.of_apply,
    physicalMetricJet_tensorCovariant hs.self_of_nhds, physicalMetricJet_dTrace hg hk h0 hs,
    CKSRound.MetricJet.momentum, CKSRound.MetricJet.tensorDivergence]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_energy {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalEnergy G K E x = (physicalMetricJet G x).energy (physicalTensorJet K x) := by
  unfold physicalEnergy CKSRound.MetricJet.energy
  rw [physicalMetricJet_scalar hg he hp hs ho, physicalMetricJet_trace hp.isHermitian,
    physicalMetricJet_normSq hp.isHermitian hks]

theorem physical_coordinate_DEC_iff {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (hk : ContDiffAt ℝ ∞ K x) (he : ∀ i, ContDiffAt ℝ ∞ (E i) x)
    (hp : (G x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalDEC G K E x ↔ CKSLocalBending.DEC (physicalMetricJet G x) (physicalTensorJet K x)
 := by
  have hn : metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) =
      CKSLocalBending.momentumSq (physicalMetricJet G x) (physicalTensorJet K x) := by
    simp only [metricPair, physicalMetricJet_momentum hg hk hp.det_pos.ne' hs]
    rfl
  unfold physicalDEC CKSLocalBending.DEC
  rw [hn, physicalMetricJet_energy hg he hp hs hks ho]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiffAt_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hβ : ContDiffAt ℝ ∞ β r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (normalEntry v β) r := by
  exact (hv.derivWithin (m := ∞) (by simp)).add
    (hβ.div (contDiffAt_id.pow 2) (pow_ne_zero _ hr))

lemma contDiffAt_correctionCoeff {v : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (correctionCoeff v) r := by
  exact (contDiffAt_id.mul ((hv.derivWithin (m := ∞) (by simp)).sub
    (hv.div contDiffAt_id hr))).div (contDiffAt_const.add (hv.pow 2))
      (ne_of_gt (by positivity))

lemma contDiffAt_correctedComponent {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : ContDiffAt ℝ ∞ v (x 0)) (ha : ContDiffAt ℝ ∞ a x) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ (correctedComponent v a) x :=
  (contDiffAt_radial (contDiffAt_correctionCoeff hv hr)).mul ha

lemma tensor_contDiffAt {u : Point → ℝ} {v : ℝ → ℝ} {L a b : Point → ℝ} {x : Point}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hL : ContDiffAt ℝ ∞ L x) (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (h0 : u x ≠ 0) : ContDiffAt ℝ ∞ (tensor u v L a b) x := by
  have hvr := (contDiffAt_radial hv).mul (coord 0).contDiff.contDiffAt
  have hs : ContDiffAt ℝ ∞ (fun y : Point => Real.sin (y 1)^2) x := by fun_prop
  have hfirst := hL.div (hu.pow 2) (pow_ne_zero _ h0)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hfirst
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact hvr.add ha
  · exact hb
  · exact contDiffAt_const
  · exact hb
  · exact (hvr.sub ha).mul hs

lemma tensor_hermitian (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) :
    (tensor u v L a b x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tensor]

lemma outerTensor_contDiffAt {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ ∞ F x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hβ : ContDiffAt ℝ ∞ β (x 0))
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hr : x 0 ≠ 0) (hp : 0 < radicand F v x) :
    ContDiffAt ℝ ∞ (outerTensor F v β a b) x :=
  tensor_contDiffAt (contDiffAt_lapse hF hv hr hp) hv
    (contDiffAt_radial (contDiffAt_normalEntry hv hβ hr))
    (contDiffAt_correctedComponent hv ha hr) (contDiffAt_correctedComponent hv hb hr)
    (lapse_pos hp).ne'

end
end CKSRealizedRound

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSAngularGeometry CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise Matrix

lemma sphericalAngularMetric_contDiff : ContDiff ℝ ∞ sphericalAngularMetric := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [sphericalAngularMetric]
  all_goals fun_prop

lemma roundAngularMetric_contDiff :
    ContDiff ℝ ∞ (fun y : CKSRealizedRound.Point => y 0 ^ 2 • sphericalAngularMetric y) := by
  have hr : ContDiff ℝ ∞ (fun y : CKSRealizedRound.Point => y 0 ^ 2) :=
    (coord 0).contDiff.pow 2
  exact hr.smul sphericalAngularMetric_contDiff

lemma roundAngularMetric_posDef {x : CKSRealizedRound.Point}
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    (x 0 ^ 2 • sphericalAngularMetric x).PosDef :=
  (sphericalAngularMetric_posDef hs).smul (sq_pos_of_ne_zero hr)

lemma roundAngularMetric_eventually_posDef {x : CKSRealizedRound.Point}
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    ∀ᶠ y in 𝓝 x, (y 0 ^ 2 • sphericalAngularMetric y).PosDef := by
  have hrn := (coord 0).continuous.continuousAt (x := x).eventually_ne hr
  have hsn := (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x).eventually_ne hs
  filter_upwards [hrn,hsn] with y hyr hys
  exact roundAngularMetric_posDef hyr hys

end
end CKSSphericalChart

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

def radicand (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  1 + bendingV R ‖x‖ ^ 2 - 2 * cartMass f₀ m R x / ‖x‖
def metric (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : Mat :=
  1 + ((radicand f₀ m R x)⁻¹-1) • vecMulVec (normal x) (normal x)
def tensor (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : Mat :=
  (normalEntry (bendingV R) (bendingBeta R) ‖x‖ / radicand f₀ m R x) •
      vecMulVec (normal x) (normal x) +
    (bendingV R ‖x‖/‖x‖) • (1-vecMulVec (normal x) (normal x)) +
    (correctionCoeff (bendingV R) ‖x‖ / ‖x‖^2) •
      canonicalT f₀ (heatTime R ‖x‖) (unitVector x)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma normal_smoothAt {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (normal : E → Fin 3 → ℝ) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact (EuclideanSpace.proj i).contDiff.contDiffAt.div (contDiffAt_norm ℝ hx)
    (norm_ne_zero_iff.mpr hx)
lemma radicand_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radicand f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n := ∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := ((bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  exact (contDiffAt_const.add (hv.pow 2)).sub
    ((contDiffAt_const.mul (cartMass_smooth f₀ hf₀ m hR hx)).div hn hr.ne')
lemma metric_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (metric f₀ m R) x := by
  have hi := (radicand_smoothAt f₀ hf₀ m hR hx).inv hp
  have hn := normal_smoothAt hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun y => (if i=j then 1 else 0) +
    ((radicand f₀ m R y)⁻¹-1)*(normal y i*normal y j)) x
  exact contDiffAt_const.add ((hi.sub contDiffAt_const).mul
    ((contDiffAt_pi.mp hn i).mul (contDiffAt_pi.mp hn j)))
lemma cartTensorHeat_component_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (i j : Ix) :
    ContDiffAt ℝ ∞ (fun y : E => canonicalT f₀ (heatTime R ‖y‖) (unitVector y) i j) x := by
  have hh : ContDiffAt ℝ ∞ (heatTime R) ‖x‖ :=
    (heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    hh.comp x (contDiffAt_norm ℝ hx (n:=∞))
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := unitVector_ne hx
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalT_joint f₀ hf₀ i j).contDiffAt (heatDomain_open.mem_nhds hz)
  exact hc.comp x (ht.prodMk (unitVector_smooth hx))
lemma cartTensorHeat_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => canonicalT f₀ (heatTime R ‖y‖) (unitVector y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact cartTensorHeat_component_smoothAt f₀ hf₀ hR hx i j
lemma tensor_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (tensor f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n:=∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)
  have hL := (contDiffAt_normalEntry hv (bendingBeta_smooth R).contDiffAt hr.ne').comp x hn
  have hc := (contDiffAt_correctionCoeff hv hr.ne').comp x hn
  have hU := radicand_smoothAt f₀ hf₀ m hR hx
  have hnormal := normal_smoothAt hx
  have hT := cartTensorHeat_smoothAt f₀ hf₀ hR hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hi := contDiffAt_pi.mp hnormal i
  have hj := contDiffAt_pi.mp hnormal j
  exact (((hL.div hU hp).mul (hi.mul hj)).add
    (((hv.comp x hn).div hn hr.ne').mul (contDiffAt_const.sub (hi.mul hj)))).add
    ((hc.div (hn.pow 2) (pow_ne_zero _ hr.ne')).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j))
lemma rankOne_positive {n : Fin 3 → ℝ} (hn : ∑ i, n i^2=1)
    {a : ℝ} (ha : 0<a) : (1+(a-1) • vecMulVec n n : Mat).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.add_apply, Matrix.vecMulVec, mul_comm,
      mul_assoc, Matrix.one_apply, eq_comm]
  · intro v hv
    have hq : 0 < ∑ i, v i^2 := by
      have h := (Matrix.PosDef.one : (1 : Mat).PosDef).dotProduct_mulVec_pos hv
      simpa [dotProduct, pow_two] using h
    have hcs : (∑ i, n i*v i)^2 ≤ ∑ i, v i^2 := by
      simpa only [hn,one_mul] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ n v
    have he : star v ⬝ᵥ ((1+(a-1) • vecMulVec n n : Mat) *ᵥ v) =
        (∑ i, v i^2)+(a-1)*(∑ i, n i*v i)^2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fin.sum_univ_succ, Matrix.one_apply]
      ring
    rw [he]
    by_cases hh : 1 ≤ a
    · have hnn := mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg (∑ i, n i*v i))
      linarith
    · have hnn := mul_nonneg (show 0≤1-a by linarith) (sub_nonneg.mpr hcs)
      have hp := mul_pos ha hq
      nlinarith
lemma metric_positive {f₀ : C(Sphere,ℝ)} {m R : ℝ} {x : E} (hx : x ≠ 0)
    (hp : 0 < radicand f₀ m R x) : (metric f₀ m R x).PosDef :=
  rankOne_positive (normal_sq hx) (inv_pos.mpr hp)
lemma tensor_hermitian (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R : ℝ)
    {x : E} (hx : x ≠ 0) : (tensor f₀ m R x).IsHermitian := by
  have hs := heatTensor_symmetric_U (heatPolynomials f₀) (smoothDatum_rapid f₀ hf₀)
    (heatTime R ‖x‖) (unitVector x) (unitVector_ne hx)
  apply Matrix.IsHermitian.ext
  intro i j
  change tensor f₀ m R x j i = tensor f₀ m R x i j
  simp only [tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, canonicalT, hs j i, mul_comm (normal x j) (normal x i)]
  simp [Matrix.one_apply,eq_comm]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma cartMass_uniform_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      |cartMass f₀ m R x| ≤ B := by
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  refine ⟨B,hB,?_⟩
  intro R hR x hx
  have hxp : x ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖x‖)
  let n : Sphere := ⟨unitVector x, by simpa only [Metric.mem_sphere,dist_zero_right] using unitVector_norm hxp⟩
  exact hbound R ‖x‖ hR hx n
lemma cartesian_radicand_positive (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      0 < radicand f₀ m R x := by
  obtain ⟨B,hB,hbound⟩ := cartMass_uniform_bound f₀ hf₀ m
  refine ⟨max 12 (4*B+1),le_max_left _ _,?_⟩
  intro R hR x hx
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRB : 4*B+1 ≤ R := (le_max_right _ _).trans hR
  have hh := denominator_lower hB.le (hbound R (by linarith) x hx) (by linarith : 4*B+1 ≤ ‖x‖)
  unfold radicand
  nlinarith [sq_nonneg (bendingV R ‖x‖)]
theorem constructed_cartesian_outer_regular
    (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      ContDiffAt ℝ ∞ (metric f₀ m R) x ∧
      ContDiffAt ℝ ∞ (tensor f₀ m R) x ∧
      (metric f₀ m R x).PosDef ∧ (tensor f₀ m R x).IsHermitian := by
  obtain ⟨R₀,hR₀,hp⟩ := cartesian_radicand_positive f₀ hf₀ m
  refine ⟨R₀,hR₀,?_⟩
  intro R hR x hx
  have h12 : 12 ≤ R := hR₀.trans hR
  have hRp : 0<R := by linarith
  have hxp : x ≠ 0 := norm_pos_iff.mp (by linarith : 0<‖x‖)
  have hpos := hp R hR x hx
  exact ⟨metric_smoothAt f₀ hf₀ m hRp hxp hpos.ne', tensor_smoothAt f₀ hf₀ m hRp hxp hpos.ne',
    metric_positive hxp hpos, tensor_hermitian f₀ hf₀ m R hxp⟩
lemma tensor_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) : tensor f₀ m R x = 0 := by
  have hRp : 0<R := by linarith
  have hv := bendingV_tail hRp hx.le
  have hvp := bendingV_tail_deriv hRp hx
  have hb := bendingBeta_tail hR hx.le
  simp [tensor,normalEntry,correctionCoeff,hv,hvp,hb]
lemma metric_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0<R)
    {x : E} (hx : 2*R^2 ≤ ‖x‖) : metric f₀ m R x = CKSADM.metric (cartB f₀ m R) x := by
  have hv := bendingV_tail hR hx
  ext i j
  simp only [metric,radicand,hv,zero_pow (by decide : (2:ℕ)≠0),add_zero,
    CKSADM.metric,cartB,Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,smul_eq_mul]
  ring
lemma metric_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) (i j : Ix) :
    Symbol 1 (fun x => metric f₀ m R x i j - (if i=j then 1 else 0)) := by
  apply (constructed_metric_decay f₀ hf₀ m hR i j).congr
  filter_upwards [eventually_norm_ge (2*R^2)] with x hx
  rw [metric_tail f₀ m (by linarith : 0<R) hx]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SmoothOrthonormalAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ G x
  frame_smooth : ∀ i, ContDiffAt ℝ ∞ (E i) x
  positive : (G x).PosDef
  symmetric : ∀ᶠ y in 𝓝 x, (G y).IsHermitian
  orthonormal : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0

structure FrameChartAt (φ : PhysicalPoint → PhysicalPoint)
    (G H : PhysicalPoint → AmbientMat) (E F : LocalFrame) (x : PhysicalPoint) : Prop where
  chart_smooth : ContDiffAt ℝ ∞ φ x
  source : SmoothOrthonormalAt G E (φ x)
  target : SmoothOrthonormalAt H F x
  frame_related : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ φ y (F i y) = E i (φ y)
  metric_related : ∀ v w, metricPair (H x) v w =
    metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma actualFrameBracket_eq_lieBracket {E : LocalFrame} {x : PhysicalPoint}
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (i j : Fin 3) :
    actualFrameBracket E x i j = VectorField.lieBracket ℝ (E i) (E j) x := by
  ext k
  simp only [actualFrameBracket,D,VectorField.lieBracket,Pi.sub_apply,
    fderiv_apply (he j),fderiv_apply (he i),ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
lemma FrameChartAt.bracket_related {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) (i j : Fin 3) :
    fderiv ℝ φ x (actualFrameBracket F x i j) = actualFrameBracket E (φ x) i j := by
  have hdφ := h.chart_smooth.differentiableAt (by simp)
  have hde k := (h.source.frame_smooth k).differentiableAt (by simp)
  have hdf k := (h.target.frame_smooth k).differentiableAt (by simp)
  have hr k : (fun y => fderiv ℝ φ y (F k y)) =ᶠ[𝓝 x] (fun y => E k (φ y)) :=
    h.frame_related.mono (fun y hy => hy k)
  rw [actualFrameBracket_eq_lieBracket hdf]
  rw [VectorField.fderiv_apply_lieBracket h.chart_smooth (by simp) (hdf j) (hdf i)]
  rw [(hr j).fderiv_eq,(hr i).fderiv_eq,
    fderiv_fun_comp x (hde j) hdφ,fderiv_fun_comp x (hde i) hdφ]
  simp only [ContinuousLinearMap.comp_apply,h.frame_related.self_of_nhds]
  exact (actualFrameBracket_eq_lieBracket hde i j).symm
lemma FrameChartAt.bracket_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameBracketCoefficient H F x = frameBracketCoefficient G E (φ x) := by
  funext i j k
  unfold frameBracketCoefficient
  rw [h.metric_related,h.bracket_related,h.frame_related.self_of_nhds k]
lemma FrameChartAt.connection_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameCoefficient H F x = frameCoefficient G E (φ x) := by
  have hs := h.source
  have ht := h.target
  rw [physical_frame_koszul (ht.metric_smooth.differentiableAt (by simp))
    (fun i => (ht.frame_smooth i).differentiableAt (by simp)) ht.positive ht.symmetric ht.orthonormal]
  rw [physical_frame_koszul (hs.metric_smooth.differentiableAt (by simp))
    (fun i => (hs.frame_smooth i).differentiableAt (by simp)) hs.positive hs.symmetric hs.orthonormal]
  rw [h.bracket_coefficients]

lemma D_chart_related {φ : PhysicalPoint → PhysicalPoint}
    {f g : PhysicalPoint → ℝ} {v w x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ x) (hf : DifferentiableAt ℝ f (φ x))
    (hvw : fderiv ℝ φ x v = w) (hfg : g =ᶠ[𝓝 x] (fun y => f (φ y))) :
    D v g x = D w f (φ x) := by
  unfold D
  rw [hfg.fderiv_eq,fderiv_fun_comp x hf hφ,ContinuousLinearMap.comp_apply,hvw]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frame_connection_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (a i j k : Fin 3) :
    D (F a x) (fun y => frameCoefficient H F y i j k) x =
      D (E a (φ x)) (fun y => frameCoefficient G E y i j k) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((frameCoefficient_contDiffAt hx.source.metric_smooth hx.source.positive.det_pos.ne'
      hx.source.frame_smooth i j k).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h] with y hy
  exact congrFun (congrFun (congrFun hy.connection_coefficients i) j) k
lemma actualFrameCurvature_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (i j k l : Fin 3) :
    actualFrameCurvature H F x i j k l = actualFrameCurvature G E (φ x) i j k l := by
  unfold actualFrameCurvature
  rw [frame_connection_direction_chart h,frame_connection_direction_chart h,
    h.self_of_nhds.connection_coefficients,h.self_of_nhds.bracket_coefficients]
lemma actualFrameScalar_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) := by
  unfold actualFrameScalar
  simp_rw [actualFrameCurvature_chart_covariance h]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frameTensor_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x)
    (hkl : ∀ v w, metricPair (L x) v w =
      metricPair (K (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)) :
    frameTensor L F x = frameTensor K E (φ x) := by
  funext i j
  unfold frameTensor
  rw [hkl,h.frame_related.self_of_nhds i,h.frame_related.self_of_nhds j]
lemma frame_tensor_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (a i j : Fin 3) :
    D (F a x) (fun y => frameTensor L F y i j) x =
      D (E a (φ x)) (fun y => frameTensor K E y i j) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((metricPair_contDiffAt hk (hx.source.frame_smooth i) (hx.source.frame_smooth j)).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h,hkl] with y hy hky
  exact congrFun (congrFun (frameTensor_chart_covariance hy hky) i) j
lemma actualFrameTensorCovariant_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (i j k : Fin 3) :
    actualFrameTensorCovariant H L F x i j k = actualFrameTensorCovariant G K E (φ x) i j k := by
  unfold actualFrameTensorCovariant
  rw [frame_tensor_direction_chart h hk hkl,h.self_of_nhds.connection_coefficients,
    frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds]

theorem actual_constraints_chart_covariance
    {φ : PhysicalPoint → PhysicalPoint} {G H K L : PhysicalPoint → AmbientMat}
    {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) ∧
    actualFrameEnergy H L F x = actualFrameEnergy G K E (φ x) ∧
    (∀ i, actualFrameMomentum H L F x i = actualFrameMomentum G K E (φ x) i)
 := by
  have hs := actualFrameScalar_chart_covariance h
  have ht := frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds
  refine ⟨hs,?_,?_⟩
  · unfold actualFrameEnergy
    rw [hs,ht]
  · intro j
    unfold actualFrameMomentum
    simp_rw [actualFrameTensorCovariant_chart_covariance h hk hkl,
      frame_tensor_direction_chart h hk hkl]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma FrameChartAt.target_adapted {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x)
    (ha : ∀ a b : Fin 2, frameBracketCoefficient G E (φ x) a.succ b.succ 0 = 0) :
    ActualAdaptedAt H F x := by
  refine ⟨h.target.metric_smooth.differentiableAt (by simp),
    (fun i => (h.target.frame_smooth i).differentiableAt (by simp)),
    h.target.positive,h.target.symmetric,h.target.orthonormal,?_⟩
  intro a b
  rw [h.bracket_coefficients]
  exact ha a b
lemma FrameChartAt.source_adapted {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x)
    (ha : ∀ a b : Fin 2, frameBracketCoefficient G E (φ x) a.succ b.succ 0 = 0) :
    ActualAdaptedAt G E (φ x) :=
  ⟨h.source.metric_smooth.differentiableAt (by simp),
    (fun i => (h.source.frame_smooth i).differentiableAt (by simp)),
    h.source.positive,h.source.symmetric,h.source.orthonormal,ha⟩

theorem physical_DEC_chart_covariance
    {φ : PhysicalPoint → PhysicalPoint} {G H K L : PhysicalPoint → AmbientMat}
    {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x)) (hl : DifferentiableAt ℝ L x)
    (hkSymm : (K (φ x)).IsHermitian) (hlSymm : (L x).IsHermitian)
    (ha : ∀ a b : Fin 2, frameBracketCoefficient G E (φ x) a.succ b.succ 0 = 0)
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) :
    physicalDEC H L F x ↔ physicalDEC G K E (φ x) := by
  have hS := h.self_of_nhds.source_adapted ha
  have hT := h.self_of_nhds.target_adapted ha
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hk hkl
  have hδ : physicalEnergy H L F x = physicalEnergy G K E (φ x) := by
    change _ = _ at hC
    rw [actualFrameEnergy_coordinate hT hlSymm, actualFrameEnergy_coordinate hS hkSymm] at hC
    exact hC
  unfold physicalDEC
  rw [← physical_momentum_frame_norm hT hl,
    ← physical_momentum_frame_norm hS (hk.differentiableAt (by simp)),hδ]
  simp_rw [hJ]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def coordinatePullback (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : AmbientMat := fun i j =>
  metricPair (G (φ x)) (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j))
def coordinatePullbackFrame (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (E : LocalFrame) : LocalFrame := fun i x => fderiv ℝ e.symm (e x) (E i (e x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma metricPair_sum_right (g : AmbientMat) (v : PhysicalPoint) (w : Fin 3 → PhysicalPoint) :
    metricPair g v (∑ i, w i) = ∑ i, metricPair g v (w i) := by
  simp only [metricPair,Fin.sum_univ_three,Pi.add_apply]
  ring
lemma coordinatePullback_pair (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x v w : PhysicalPoint) :
    metricPair (coordinatePullback φ G x) v w =
      metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  conv_rhs => arg 2; rw [direction_expansion v]
  conv_rhs => arg 3; rw [direction_expansion w]
  simp only [map_sum,map_smul]
  simp only [metricPair_sum_left,metricPair_sum_right,metricPair_smul_left,
    metricPair_smul_right,Finset.mul_sum]
  change (∑ i, ∑ j, metricPair (G (φ x))
    (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j)) * v i * w j) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma metricPair_dotProduct (g : AmbientMat) (v : PhysicalPoint) :
    metricPair g v v = star v ⬝ᵥ (g *ᵥ v) := by
  simp only [metricPair,dotProduct,mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma coordinatePullback_symmetric {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).IsHermitian) :
    (coordinatePullback φ G x).IsHermitian := by
  ext i j
  simpa only [conjTranspose_apply,star_trivial,coordinatePullback] using
    metricPair_symm hg (fderiv ℝ φ x (CKSRealizedRound.basis j))
      (fderiv ℝ φ x (CKSRealizedRound.basis i))
lemma coordinatePullback_positive {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).PosDef)
    (hφ : Function.Injective (fderiv ℝ φ x)) : (coordinatePullback φ G x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (coordinatePullback_symmetric hg.isHermitian)
  intro v hv
  rw [← metricPair_dotProduct,coordinatePullback_pair,metricPair_dotProduct]
  exact hg.dotProduct_mulVec_pos (fun h => hv (hφ (h.trans (map_zero _).symm)))
lemma coordinatePullback_smooth {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ ∞ φ x) (hg : ContDiffAt ℝ ∞ G (φ x)) :
    ContDiffAt ℝ ∞ (coordinatePullback φ G) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact metricPair_contDiffAt (hg.comp x hφ)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
lemma chart_fderiv_left_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e.symm (e x) (fderiv ℝ e x v) = v := by
  have hEq : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
  have hh := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hi he,fderiv_id] at hh
  exact congrArg (fun T : PhysicalPoint →L[ℝ] PhysicalPoint => T v) hh
lemma chart_fderiv_right_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e x (fderiv ℝ e.symm (e x) v) = v := by
  have hh := chart_fderiv_left_inverse e.symm (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he) v
  simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using hh
lemma coordinatePullbackFrame_smooth
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (E : LocalFrame)
    {x : PhysicalPoint} (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hE : ∀ i, ContDiffAt ℝ ∞ (E i) (e x)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (coordinatePullbackFrame e E i) x :=
  ((hi.fderiv_right (by simp)).comp x he).clm_apply ((hE i).comp x he)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem smooth_coordinate_pullback_frame
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hE : ∀ y ∈ e.target, SmoothOrthonormalAt G E y)
    {x : PhysicalPoint} (hx : x ∈ e.source) :
    FrameChartAt e G (coordinatePullback e G) E (coordinatePullbackFrame e E) x
 := by
  have hes y (hy : y ∈ e.source) : ContDiffAt ℝ ∞ e y :=
    he.contDiffAt (e.open_source.mem_nhds hy)
  have his y (hy : y ∈ e.source) : ContDiffAt ℝ ∞ e.symm (e y) :=
    hi.contDiffAt (e.open_target.mem_nhds (e.map_source hy))
  have hed y hy := (hes y hy).differentiableAt (by simp)
  have hid y hy := (his y hy).differentiableAt (by simp)
  have hEinj : Function.Injective (fderiv ℝ e x) := by
    intro v w h
    have hh := congrArg (fderiv ℝ e.symm (e x)) h
    simpa only [chart_fderiv_left_inverse e hx (hed x hx) (hid x hx)] using hh
  have hSrc := hE (e x) (e.map_source hx)
  have hRel : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ e y (coordinatePullbackFrame e E i y) = E i (e y) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy i
    exact chart_fderiv_right_inverse e hy (hed y hy) (hid y hy) _
  have hOrth : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (coordinatePullback e G y) (coordinatePullbackFrame e E i y)
        (coordinatePullbackFrame e E j y) = if i=j then 1 else 0 := by
    filter_upwards [hRel,(e.continuousAt hx).eventually hSrc.orthonormal] with y hyr hyo i j
    rw [coordinatePullback_pair,hyr i,hyr j,hyo]
  refine ⟨hes x hx,hSrc,?_,hRel,coordinatePullback_pair e G x⟩
  refine ⟨coordinatePullback_smooth (hes x hx) hSrc.metric_smooth,
    coordinatePullbackFrame_smooth e E (hes x hx) (his x hx) hSrc.frame_smooth,
    coordinatePullback_positive hSrc.positive hEinj,?_,hOrth⟩
  exact ((e.continuousAt hx).eventually hSrc.symmetric).mono fun _ h => coordinatePullback_symmetric h
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
theorem actualFrameTensorCovariant_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k =
      coordinateTensorCovariant G K (E i x) (E j x) (E k x) x := by
  have ho := h.orthonormal.self_of_nhds
  have hleft := metricPair_frame_left (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E j) x) (E k x)
  have hright := metricPair_frame_right (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E k) x) (E j x)
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
    metricPair (K x) (E a x) (E k x)) = _ at hleft
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
    metricPair (K x) (E j x) (E a x)) = _ at hright
  rw [coordinateTensorCovariant_product_rule hk ((h.frame_smooth j).differentiableAt (by simp)) ((h.frame_smooth k).differentiableAt (by simp))]
  unfold actualFrameTensorCovariant
  rw [Finset.sum_add_distrib]
  change D (E i x) (fun y => metricPair (K y) (E j y) (E k y)) x -
    ((∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
      metricPair (K x) (E a x) (E k x)) +
     ∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
      metricPair (K x) (E j x) (E a x)) = _
  rw [hleft,hright]
  ring

lemma frame_trace_derivative_general {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x) (hk : DifferentiableAt ℝ K x)
    (e : PhysicalPoint) :
    (∑ i, D e (fun y => frameTensor K E y i i) x)=
      D e (fun y => ((G y)⁻¹*K y).trace) x := by
  change (∑ i, D e (fun y => metricPair (K y) (E i y) (E i y)) x) = _
  rw [← D_sum3 e _ (fun i => metricPair_differentiableAt hk ((h.frame_smooth i).differentiableAt (by simp)) ((h.frame_smooth i).differentiableAt (by simp)))]
  apply D_congr
  filter_upwards [h.orthonormal] with y hy
  exact frame_trace_exact (K y) (e := Matrix.of (fun i j => E i y j)) hy

theorem actualFrameEnergy_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x =
      (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 := by
  have ho := h.orthonormal.self_of_nhds
  have ht := frame_trace_exact (K x) (e := Matrix.of (fun i j => E i x j)) ho
  have hn := frame_tensor_norm_exact hk (e := Matrix.of (fun i j => E i x j)) ho
  change (∑ i, metricPair (K x) (E i x) (E i x))=_ at ht
  change (∑ i, ∑ j, (metricPair (K x) (E i x) (E j x))^2)=_ at hn
  unfold actualFrameEnergy frameTensor
  rw [ht,hn]

theorem actualFrameMomentum_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (j : Fin 3) :
    actualFrameMomentum G K E x j=coordinateMomentum G K x (E j x) := by
  have ht := frame_trace_exact
    (Matrix.of (fun a b => coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x))
    (e := Matrix.of (fun a b => E a x b)) h.orthonormal.self_of_nhds
  change (∑ i, metricPair
    (fun a b => coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (E j x) x) (E i x) (E i x)) = _ at ht
  have hd : (∑ i, actualFrameTensorCovariant G K E x i i j) =
      ((G x)⁻¹ * Matrix.of (fun a b => coordinateTensorCovariant G K
        (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x)).trace := by
    rw [← ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualFrameTensorCovariant_coordinate_general h hk]
    exact coordinateTensorCovariant_bilinear G K x (E i x) (E i x) (E j x)
  unfold actualFrameMomentum coordinateMomentum
  rw [hd,frame_trace_derivative_general h hk]

theorem physical_momentum_frame_norm_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) :
    (∑ a, (actualFrameMomentum G K E x a)^2)=
      metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) := by
  conv_lhs => arg 2; ext a; rw [actualFrameMomentum_coordinate_general h hk,coordinateMomentum_expansion]
  exact covector_frame_square (momentumCovector G K x)
    (e := Matrix.of (fun i j => E i x j)) h.orthonormal.self_of_nhds

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem smooth_coordinate_DEC_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hE : ∀ y ∈ e.target, SmoothOrthonormalAt G E y)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) ↔
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x))
 := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact smooth_coordinate_pullback_frame e he hi G E hE hy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkSymm := coordinatePullback_symmetric hs
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  have hδ : physicalEnergy (coordinatePullback e G) (coordinatePullback e K)
      (coordinatePullbackFrame e E) x = physicalEnergy G K E (e x) := by
    rw [actualFrameEnergy_coordinate_general hc.target hkSymm,
      actualFrameEnergy_coordinate_general hc.source hs] at hC
    exact hC
  rw [← physical_coordinate_DEC_iff hc.target.metric_smooth hk' hc.target.frame_smooth
    hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    ← physical_coordinate_DEC_iff hc.source.metric_smooth hK hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal]
  unfold physicalDEC
  rw [← physical_momentum_frame_norm_general hc.target (hk'.differentiableAt (by simp)),
    ← physical_momentum_frame_norm_general hc.source (hK.differentiableAt (by simp)), hδ]
  simp_rw [hJ]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma smooth_coordinate_pullback_frame_at
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hSrc : SmoothOrthonormalAt G E (e x)) :
    FrameChartAt e G (coordinatePullback e G) E (coordinatePullbackFrame e E) x := by
  have hed := he.differentiableAt (by simp)
  have hid := hi.differentiableAt (by simp)
  have hEinj : Function.Injective (fderiv ℝ e x) := by
    intro v w h
    have hh := congrArg (fderiv ℝ e.symm (e x)) h
    simpa only [chart_fderiv_left_inverse e hx hed hid] using hh
  have hRel : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ e y (coordinatePullbackFrame e E i y) = E i (e y) := by
    filter_upwards [e.open_source.mem_nhds hx,(he.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      he.continuousAt.eventually ((hi.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))] with y hy hey hiy i
    exact chart_fderiv_right_inverse e hy (hey.differentiableAt (by simp))
      (hiy.differentiableAt (by simp)) _
  have hOrth : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (coordinatePullback e G y) (coordinatePullbackFrame e E i y)
        (coordinatePullbackFrame e E j y) = if i=j then 1 else 0 := by
    filter_upwards [hRel,he.continuousAt.eventually hSrc.orthonormal] with y hyr hyo i j
    rw [coordinatePullback_pair,hyr i,hyr j,hyo]
  refine ⟨he,hSrc,?_,hRel,coordinatePullback_pair e G x⟩
  refine ⟨coordinatePullback_smooth he hSrc.metric_smooth,
    coordinatePullbackFrame_smooth e E he hi hSrc.frame_smooth,
    coordinatePullback_positive hSrc.positive hEinj,?_,hOrth⟩
  exact (he.continuousAt.eventually hSrc.symmetric).mono fun _ h => coordinatePullback_symmetric h

theorem local_coordinate_DEC_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) ↔
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkSymm := coordinatePullback_symmetric hs
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  have hδ : physicalEnergy (coordinatePullback e G) (coordinatePullback e K)
      (coordinatePullbackFrame e E) x = physicalEnergy G K E (e x) := by
    rw [actualFrameEnergy_coordinate_general hc.target hkSymm,
      actualFrameEnergy_coordinate_general hc.source hs] at hC
    exact hC
  rw [← physical_coordinate_DEC_iff hc.target.metric_smooth hk' hc.target.frame_smooth
    hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    ← physical_coordinate_DEC_iff hc.source.metric_smooth hK hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal]
  unfold physicalDEC
  rw [← physical_momentum_frame_norm_general hc.target (hk'.differentiableAt (by simp)),
    ← physical_momentum_frame_norm_general hc.source (hK.differentiableAt (by simp)), hδ]
  simp_rw [hJ]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
def sphericalMap (x : PhysicalPoint) : PhysicalPoint := toPoint (x 0 • sphereParam x)
def sphericalBasis (x : PhysicalPoint) (i : Fin 3) : E :=
  ![sphereParam x,x 0 • thetaFrame x,x 0 • phiFrame x] i
def physicalMetric (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : PhysicalPoint) : AmbientMat :=
  metric f₀ m R (toPoint.symm x)
def physicalTensor (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : PhysicalPoint) : AmbientMat :=
  tensor f₀ m R (toPoint.symm x)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma sphericalMap_smooth : ContDiff ℝ ∞ sphericalMap :=
  toPoint.contDiff.comp ((coord 0).contDiff.smul sphereParam_smooth)
lemma sphericalMap_euclidean (x : PhysicalPoint) :
    toPoint.symm (sphericalMap x) = x 0 • sphereParam x := toPoint.symm_apply_apply _
lemma sphericalMap_norm {x : PhysicalPoint} (hx : 0 < x 0) :
    ‖toPoint.symm (sphericalMap x)‖ = x 0 := by
  rw [sphericalMap_euclidean,norm_smul,Real.norm_eq_abs,abs_of_pos hx,sphereParam_norm,mul_one]
lemma sphericalMap_unit {x : PhysicalPoint} (hx : 0 < x 0) :
    unitVector (toPoint.symm (sphericalMap x))=sphereParam x := by
  rw [unitVector,sphericalMap_norm hx,sphericalMap_euclidean,smul_smul,
    inv_mul_cancel₀ hx.ne',one_smul]
lemma sphericalMap_fderiv (x : PhysicalPoint) (i : Fin 3) :
    fderiv ℝ sphericalMap x (basis i) = toPoint (sphericalBasis x i) := by
  have hd : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0 • sphereParam y) x :=
    (coord 0).differentiableAt.smul (sphereParam_smooth.differentiable (by simp) x)
  rw [show sphericalMap = toPoint ∘ (fun y : PhysicalPoint => y 0 • sphereParam y) from rfl,
    fderiv_comp x toPoint.differentiableAt hd,ContinuousLinearEquiv.fderiv,
    ContinuousLinearMap.comp_apply]
  change toPoint (fderiv ℝ (fun y : PhysicalPoint => y 0 • sphereParam y) x (basis i)) = toPoint (sphericalBasis x i)
  apply congrArg toPoint
  change fderiv ℝ (fun y : PhysicalPoint => (coord 0) y • sphereParam y) x (basis i) = _
  rw [fderiv_fun_smul (coord 0).differentiableAt (sphereParam_smooth.differentiable (by simp) x)]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, fderiv_sphereParam]
  have hc : fderiv ℝ (coord 0) x (basis i) = if 0=i then 1 else 0 := D_coord i 0 x
  rw [hc]
  fin_cases i <;> simp [sphericalBasis,chartVector] <;> rfl
lemma sphericalMap_mass (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) : cartMass f₀ m R (toPoint.symm (sphericalMap x)) = outerMass f₀ m R x := by
  rw [cartMass,sphericalMap_norm hx,sphericalMap_unit hx]
  rfl
lemma sphericalMap_radicand (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) : radicand f₀ m R (toPoint.symm (sphericalMap x)) =
      CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) x := by
  rw [radicand,sphericalMap_norm hx,sphericalMap_mass f₀ m R hx]
  rfl
lemma metricPair_toPoint (M : AmbientMat) (v w : E) :
    metricPair M (toPoint v) (toPoint w) = pair M v w := by
  unfold metricPair pair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change M i j*v i*w j=v i*w j*M i j
  ring
lemma pair_add_matrix (A B : AmbientMat) (v w : E) : pair (A+B) v w=pair A v w+pair B v w := by
  simp [pair,mul_add,Finset.sum_add_distrib]
lemma pair_smul_matrix (c : ℝ) (A : AmbientMat) (v w : E) : pair (c • A) v w=c*pair A v w := by
  simp only [pair,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma pair_one (v w : E) : pair (1 : AmbientMat) v w=∑ i, v i*w i := by
  simp [pair,Matrix.one_apply]
lemma pair_rankOne (n : Fin 3 → ℝ) (v w : E) :
    pair (vecMulVec n n) v w=(∑ i,n i*v i)*(∑ i,n i*w i) := by
  simp only [pair,Matrix.vecMulVec_apply,Fin.sum_univ_three]
  ring
lemma normal_sphericalMap {x : PhysicalPoint} (hx : 0 < x 0) :
    normal (toPoint.symm (sphericalMap x)) = fun i => sphereParam x i := by
  funext i
  change (toPoint.symm (sphericalMap x)) i / ‖toPoint.symm (sphericalMap x)‖ = sphereParam x i
  rw [sphericalMap_norm hx,sphericalMap_euclidean]
  change (x 0 * sphereParam x i)/x 0=sphereParam x i
  field_simp
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_one_symm (v w : E) : pair (1 : AmbientMat) v w=pair (1 : AmbientMat) w v := by
  rw [pair_one,pair_one]
  apply Finset.sum_congr rfl
  intro i _
  ring
def unitBasis (x : PhysicalPoint) (i : Fin 3) : E := ![sphereParam x,thetaFrame x,phiUnit x] i
def sphericalScale (x : PhysicalPoint) (i : Fin 3) : ℝ := ![1,x 0,x 0*Real.sin (x 1)] i
lemma sphericalBasis_scaled (x : PhysicalPoint) (i : Fin 3) :
    sphericalBasis x i=sphericalScale x i • unitBasis x i := by
  fin_cases i <;> simp [sphericalBasis,sphericalScale,unitBasis,phiFrame,smul_smul]
lemma pair_one_unitBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (1 : AmbientMat) (unitBasis x i) (unitBasis x j)=if i=j then 1 else 0 := by
  have hnn : pair (1 : AmbientMat) (sphereParam x) (sphereParam x)=1 := by
    rw [pair_one]
    simpa only [sq] using unit_sum_sq (sphereParam_norm x)
  have hnθ : pair (1 : AmbientMat) (sphereParam x) (thetaFrame x)=0 := by
    rw [pair_one]; exact theta_tangent x
  have hnu : pair (1 : AmbientMat) (sphereParam x) (phiUnit x)=0 := by
    rw [pair_one]; exact unit_tangent x
  have hθθ : pair (1 : AmbientMat) (thetaFrame x) (thetaFrame x)=1 := by
    rw [pair_one]; simpa only [sq] using theta_unit x
  have huu : pair (1 : AmbientMat) (phiUnit x) (phiUnit x)=1 := by
    rw [pair_one]; simpa only [sq] using unit_unit x
  have hθu : pair (1 : AmbientMat) (thetaFrame x) (phiUnit x)=0 := by
    rw [pair_one]; exact theta_unit_orthogonal x
  have hθn := (pair_one_symm (thetaFrame x) (sphereParam x)).trans hnθ
  have hun := (pair_one_symm (phiUnit x) (sphereParam x)).trans hnu
  have huθ := (pair_one_symm (phiUnit x) (thetaFrame x)).trans hθu
  fin_cases i <;> fin_cases j <;>
    simp [unitBasis,hnn,hnθ,hnu,hθθ,huu,hθu,hθn,hun,huθ]
lemma pair_one_sphericalBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (1 : AmbientMat) (sphericalBasis x i) (sphericalBasis x j)=
      if i=j then sphericalScale x i ^ 2 else 0 := by
  rw [sphericalBasis_scaled,sphericalBasis_scaled,pair_smul_left,pair_smul_right,
    pair_one_unitBasis]
  split_ifs with h
  · subst j; ring
  · ring
lemma normalDot_sphericalBasis (x : PhysicalPoint) (i : Fin 3) :
    (∑ j, sphereParam x j * sphericalBasis x i j)=if i=0 then 1 else 0 := by
  rw [← pair_one,sphericalBasis_scaled,pair_smul_right]
  change sphericalScale x i * pair (1 : AmbientMat) (unitBasis x 0) (unitBasis x i)=_
  rw [pair_one_unitBasis]
  fin_cases i <;> simp [sphericalScale]
lemma pair_rankOne_sphericalBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (vecMulVec (fun a => sphereParam x a) (fun a => sphereParam x a))
      (sphericalBasis x i) (sphericalBasis x j)=
        (if i=0 then 1 else 0)*(if j=0 then 1 else 0) := by
  rw [pair_rankOne,normalDot_sphericalBasis,normalDot_sphericalBasis]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_sum_right (M : AmbientMat) (v : E) (w : Fin 3 → E) :
    pair M v (∑ i,w i)=∑ i,pair M v (w i) := by
  simp [Fin.sum_univ_three,pair_add_right]
lemma sphericalMap_fderiv_component (x v : PhysicalPoint) (j : Fin 3) :
    pair (1 : AmbientMat) (unitBasis x j) (toPoint.symm (fderiv ℝ sphericalMap x v))=
      sphericalScale x j*v j := by
  conv_lhs => pattern v; rw [direction_expansion v]
  simp only [map_sum,map_smul,sphericalMap_fderiv,toPoint.symm_apply_apply,
    pair_sum_right,pair_smul_right,sphericalBasis_scaled,pair_one_unitBasis]
  simp [mul_ite,Finset.sum_ite_eq,mul_comm]
lemma sphericalMap_fderiv_injective {x : PhysicalPoint} (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : Function.Injective (fderiv ℝ sphericalMap x) := by
  intro v w h
  funext j
  have hh := congrArg (fun z => pair (1 : AmbientMat) (unitBasis x j) (toPoint.symm z)) h
  rw [sphericalMap_fderiv_component,sphericalMap_fderiv_component] at hh
  have hscale : sphericalScale x j≠0 := by
    fin_cases j <;> simp [sphericalScale,hx,hs]
  exact mul_left_cancel₀ hscale hh
noncomputable def sphericalDerivativeEquiv (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : PhysicalPoint ≃L[ℝ] PhysicalPoint :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ sphericalMap x)
    (LinearMap.ker_eq_bot.mpr (sphericalMap_fderiv_injective hx hs))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (sphericalMap_fderiv_injective hx hs)))
lemma sphericalDerivative_hasFDerivAt (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : HasFDerivAt sphericalMap (sphericalDerivativeEquiv x hx hs : PhysicalPoint →L[ℝ] PhysicalPoint) x :=
  (sphericalMap_smooth.differentiable (by simp) x).hasFDerivAt
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable def sphericalChart (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : OpenPartialHomeomorph PhysicalPoint PhysicalPoint :=
  sphericalMap_smooth.contDiffAt.toOpenPartialHomeomorph sphericalMap
    (sphericalDerivative_hasFDerivAt x hx hs) (by simp)
@[simp] lemma sphericalChart_coe (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : (sphericalChart x hx hs : PhysicalPoint → PhysicalPoint) = sphericalMap := rfl
lemma sphericalChart_mem (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : x ∈ (sphericalChart x hx hs).source :=
  sphericalMap_smooth.contDiffAt.mem_toOpenPartialHomeomorph_source
    (sphericalDerivative_hasFDerivAt x hx hs) (by simp)
lemma sphericalChart_inverse_smooth (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) :
    ∀ᶠ y in 𝓝 (sphericalMap x), ContDiffAt ℝ ∞ (sphericalChart x hx hs).symm y := by
  let e := sphericalChart x hx hs
  have hex : x ∈ e.source := sphericalChart_mem x hx hs
  have hix := e.left_inv hex
  have hr : ∀ᶠ z in 𝓝 x, z 0≠0 ∧ Real.sin (z 1)≠0 := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually_ne hx,
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs]
      with z hz hsz
    exact ⟨hz,hsz⟩
  have hnear : ∀ᶠ y in 𝓝 (e x), e.symm y 0≠0 ∧ Real.sin (e.symm y 1)≠0 :=
    (e.symm.continuousAt (e.map_source hex)).eventually (hix ▸ hr)
  filter_upwards [e.open_target.mem_nhds (e.map_source hex),hnear] with y hy hreg
  exact e.contDiffAt_symm hy
    (sphericalDerivative_hasFDerivAt (e.symm y) hreg.1 hreg.2)
    sphericalMap_smooth.contDiffAt
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem spherical_metric_pullback (f₀ : C(Sphere,ℝ)) (m R : ℝ) {x : PhysicalPoint}
    (hx : 0 < x 0) (hp : 0 < radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    coordinatePullback sphericalMap (physicalMetric f₀ m R) x =
      outerMetric (outerMass f₀ m R) (bendingV R) x := by
  have hA := sphericalMap_radicand f₀ m R hx
  have hL : lapse (outerMass f₀ m R) (bendingV R) x ^ 2 =
      radicand f₀ m R (toPoint.symm (sphericalMap x)) := by
    rw [hA,lapse,Real.sq_sqrt (hA ▸ hp.le)]
  ext i j
  change metricPair (metric f₀ m R (toPoint.symm (sphericalMap x)))
    (fderiv ℝ sphericalMap x (basis i)) (fderiv ℝ sphericalMap x (basis j)) = _
  rw [sphericalMap_fderiv,sphericalMap_fderiv,metricPair_toPoint,metric,
    pair_add_matrix,pair_smul_matrix,normal_sphericalMap hx,
    pair_one_sphericalBasis,pair_rankOne_sphericalBasis]
  fin_cases i <;> fin_cases j <;>
    simp [outerMetric,CKSRealizedRound.metric,sphericalScale,hL]
  ring
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_sub_matrix (A B : AmbientMat) (v w : E) : pair (A-B) v w=pair A v w-pair B v w := by
  simp [pair,mul_sub,Finset.sum_sub_distrib]
lemma heat_sphericalBasis (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (R : ℝ)
    (x : PhysicalPoint) (i j : Fin 3) :
    pair (canonicalT f₀ (heatTime R (x 0)) (sphereParam x))
      (sphericalBasis x i) (sphericalBasis x j) = x 0 ^ 2 *
      (!![0,0,0; 0,outerA f₀ R x,outerPhi f₀ R x;
          0,outerPhi f₀ R x,-outerA f₀ R x*Real.sin (x 1)^2] : AmbientMat) i j := by
  let T := canonicalT f₀ (heatTime R (x 0)) (sphereParam x)
  have hN : ∀ j, ∑ i, sphereParam x i*T i j=0 :=
    heatTensor_tangent (heatPolynomials f₀) _ (sphereParam_norm x)
  have hS : ∀ i j, T i j=T j i :=
    heatTensor_symmetric (heatPolynomials f₀) (smoothDatum_rapid f₀ hf₀) _ (sphereParam_norm x)
  have hTr : ∑ i,T i i=0 := heatTensor_trace_zero (heatPolynomials f₀) _ (sphereParam_norm x)
  have hn (v : E) : pair T (sphereParam x) v=0 := pair_normal T _ _ hN
  have hn' (v : E) : pair T v (sphereParam x)=0 := (pair_symm T hS _ _).trans (hn v)
  have hu : pair T (phiUnit x) (phiUnit x) = -pair T (thetaFrame x) (thetaFrame x) := by
    have hh := pair_trace T x hN
    rw [hTr] at hh
    linarith
  have htu : pair T (phiUnit x) (thetaFrame x)=pair T (thetaFrame x) (phiUnit x) :=
    pair_symm T hS _ _
  change pair T (sphericalBasis x i) (sphericalBasis x j)=_
  fin_cases i <;> fin_cases j <;>
    simp [sphericalBasis,phiFrame,hn,hn',hu,htu,outerA,outerPhi,chartTensorA,
      chartTensorPhi,tensorA,tensorPhi,tensorB,T,pair_smul_left,pair_smul_right] <;> ring

theorem spherical_tensor_pullback (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R : ℝ)
    {x : PhysicalPoint} (hx : 0 < x 0)
    (hp : 0 < radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    coordinatePullback sphericalMap (physicalTensor f₀ m R) x =
      outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R)
        (outerA f₀ R) (outerPhi f₀ R) x := by
  have hA := sphericalMap_radicand f₀ m R hx
  have hL : lapse (outerMass f₀ m R) (bendingV R) x ^ 2 =
      radicand f₀ m R (toPoint.symm (sphericalMap x)) := by
    rw [hA,lapse,Real.sq_sqrt (hA ▸ hp.le)]
  ext i j
  change metricPair (tensor f₀ m R (toPoint.symm (sphericalMap x)))
    (fderiv ℝ sphericalMap x (basis i)) (fderiv ℝ sphericalMap x (basis j)) = _
  rw [sphericalMap_fderiv,sphericalMap_fderiv,metricPair_toPoint,tensor,
    sphericalMap_norm hx,sphericalMap_unit hx,normal_sphericalMap hx]
  simp only [pair_add_matrix,pair_smul_matrix,pair_sub_matrix,
    pair_one_sphericalBasis,pair_rankOne_sphericalBasis,heat_sphericalBasis f₀ hf₀]
  fin_cases i <;> fin_cases j <;>
    simp [outerTensor,CKSRealizedRound.tensor,sphericalScale,hL,correctedComponent,radial] <;>
      field_simp
  ring
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma coordinatePullback_symm
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (G : PhysicalPoint → AmbientMat)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x)) :
    coordinatePullback e.symm (coordinatePullback e G) (e x) = G (e x) := by
  ext i j
  change metricPair (coordinatePullback e G (e.symm (e x)))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis i))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis j)) = _
  rw [e.left_inv hx,coordinatePullback_pair,
    chart_fderiv_right_inverse e hx he hi,chart_fderiv_right_inverse e hx he hi]
  simp [metricPair,CKSRealizedRound.basis,Pi.single_apply,mul_ite]
lemma physicalMetricJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalMetricJet G x = physicalMetricJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  have hd (a i j) : D (CKSRealizedRound.basis a) (fun y => G y i j) =ᶠ[𝓝 x]
      D (CKSRealizedRound.basis a) (fun y => H y i j) :=
    (hc i j).eventually_nhds.mono fun _ hh => D_congr hh _
  unfold physicalMetricJet
  congr 1
  · exact congrArg Inv.inv h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
  · funext a b i j
    exact D_congr (hd b i j) _
lemma physicalTensorJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalTensorJet G x = physicalTensorJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  unfold physicalTensorJet
  congr 1
  · exact h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
theorem local_coordinate_DEC_pushforward
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt (coordinatePullback e G) E y)
    (hK : ContDiffAt ℝ ∞ (coordinatePullback e K) x)
    (hs : (coordinatePullback e K x).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) ↔
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) := by
  have hEq (A : PhysicalPoint → AmbientMat) :
      coordinatePullback e.symm (coordinatePullback e A) =ᶠ[𝓝 (e x)] A := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),hi,
      (e.symm.continuousAt (e.map_source hx)).eventually (e.left_inv hx ▸ he)] with y hy hiy hey
    have hh := coordinatePullback_symm e A (e.map_target hy)
      (hey.differentiableAt (by simp)) (by simpa only [e.right_inv hy] using hiy.differentiableAt (by simp))
    simpa only [e.right_inv hy] using hh
  have h := local_coordinate_DEC_pullback e.symm (coordinatePullback e G)
    (coordinatePullback e K) E (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he)
    (by simpa only [e.left_inv hx] using hE)
    (by simpa only [e.left_inv hx] using hK)
    (by simpa only [e.left_inv hx] using hs)
  rw [physicalMetricJet_congr (hEq G),physicalTensorJet_congr (hEq K),e.left_inv hx] at h
  exact h
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma outer_physical_DEC_iff {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ ∞ F x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hβ : ContDiffAt ℝ ∞ β (x 0)) (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) (hp : 0 < radicand F v x) :
    CKSAngularGeometry.physicalDEC (outerMetric F v) (outerTensor F v β a b)
      (fun i y => CKSAngularGeometry.adaptedFrame (lapse F v y)
        (y 0 ^ 2 • sphericalAngularMetric y) 0 i) x ↔
    CKSLocalBending.DEC (metricJet (lapse F v) x)
      (tensorJet (lapse F v) v (radial (normalEntry v β))
        (correctedComponent v a) (correctedComponent v b) x) := by
  have hu := contDiffAt_lapse hF hv hr hp
  have hg := roundAngularMetric_contDiff.contDiffAt (x := x)
  have h0 := (lapse_pos hp).ne'
  have hpos := roundAngularMetric_posDef hr hs
  have hG : outerMetric F v = fun y => CKSAngularGeometry.foliationMetric (lapse F v y)
      (y 0 ^ 2 • sphericalAngularMetric y) 0 := funext (outerMetric_foliation F v)
  have hGsm : ContDiffAt ℝ ∞ (outerMetric F v) x := by
    rw [hG]
    exact CKSAngularGeometry.foliationMetric_contDiffAt hu hg contDiffAt_const h0
  have he (i) := CKSAngularGeometry.adaptedFrame_contDiffAt hu hg
    (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) hpos i
  have had := (CKSAngularGeometry.foliation_actualAdaptedAt hu hg
    (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) h0
      (roundAngularMetric_eventually_posDef hr hs)).self_of_nhds
  rw [← hG] at had
  exact CKSAngularGeometry.physical_coordinate_DEC_iff hGsm
    (outerTensor_contDiffAt hF hv hβ ha hb hr hp) he had.2.2.1 had.2.2.2.1
      (tensor_hermitian ..) had.2.2.2.2.1

theorem constructed_outer_physical_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
    3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
    CKSAngularGeometry.physicalDEC
      (outerMetric (outerMass f₀ m R) (bendingV R))
      (outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R)
        (outerA f₀ R) (outerPhi f₀ R))
      (fun i y => CKSAngularGeometry.adaptedFrame
        (lapse (outerMass f₀ m R) (bendingV R) y)
        (y 0 ^ 2 • sphericalAngularMetric y) 0 i) x
 := by
  obtain ⟨R₁,hR₁,hdec⟩ := constructed_outer_DEC f₀ hf₀ m
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  refine ⟨max R₁ (4*M),hR₁.trans (le_max_left _ _),?_⟩
  intro R hR x hr hs
  have hRR : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR12 : 12 ≤ R := hR₁.trans hRR
  have hRM : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  have hxm : x ∈ positiveChart := hrp
  have hF := (outerMass_smooth f₀ hf₀ m hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hv := (bendingV_smooth hRp).contDiffAt (isOpen_Ioi.mem_nhds hrp)
  have ha := (outerA_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hb := (outerPhi_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hp : 0 < radicand (outerMass f₀ m R) (bendingV R) x :=
    CKSAngularGeometry.outer_radicand_positive hrp (hbound R hR12 x hr hs).1 (by linarith)
  exact (outer_physical_DEC_iff hF hv (bendingBeta_smooth R).contDiffAt ha hb
    hrp.ne' hs hp).mpr (hdec R hRR x hr hs)

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set CKSSphericalChart CKSRealizedRound
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma SmoothOrthonormalAt.congr_metric {G H : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (hg : SmoothOrthonormalAt G E x)
    (h : H =ᶠ[𝓝 x] G) : SmoothOrthonormalAt H E x := by
  refine ⟨hg.metric_smooth.congr_of_eventuallyEq h, hg.frame_smooth, ?_, ?_, ?_⟩
  · rw [h.self_of_nhds]
    exact hg.positive
  · filter_upwards [h,hg.symmetric] with y hy hs
    rwa [hy]
  · filter_upwards [h,hg.orthonormal] with y hy ho
    rwa [hy]
lemma round_smoothOrthonormalAt {F : CKSRealizedRound.Point → ℝ} {v : ℝ → ℝ}
    {x : PhysicalPoint} (hF : ContDiffAt ℝ ∞ F x) (hv : ContDiffAt ℝ ∞ v (x 0))
    (hr : x 0≠0) (hs : Real.sin (x 1)≠0) (hp : 0 < CKSRealizedRound.radicand F v x) :
    SmoothOrthonormalAt (outerMetric F v)
      (fun i y => adaptedFrame (lapse F v y) (y 0^2 • sphericalAngularMetric y) 0 i) x := by
  have hu := contDiffAt_lapse hF hv hr hp
  have hg := roundAngularMetric_contDiff.contDiffAt (x := x)
  have h0 := (lapse_pos hp).ne'
  have hpos := roundAngularMetric_posDef hr hs
  have hG : outerMetric F v = fun y => foliationMetric (lapse F v y)
      (y 0 ^ 2 • sphericalAngularMetric y) 0 := funext (outerMetric_foliation F v)
  have had := (foliation_actualAdaptedAt hu hg
    (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) h0
      (roundAngularMetric_eventually_posDef hr hs)).self_of_nhds
  rw [←hG] at had
  refine ⟨?_,?_,had.2.2.1,had.2.2.2.1,had.2.2.2.2.1⟩
  · rw [hG]
    exact foliationMetric_contDiffAt hu hg contDiffAt_const h0
  · intro i
    exact adaptedFrame_contDiffAt hu hg (contDiffAt_const (c := (0 : CKSAngularGeometry.Point))) hpos i
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spherical_physical_DEC_iff (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : PhysicalPoint} (hx : 0<x 0) (hs : Real.sin (x 1)≠0)
    (hp : 0<radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    CKSLocalBending.DEC (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x))
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) ↔
    CKSLocalBending.DEC (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x)
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  have hF (y : PhysicalPoint) (hy : 0<y 0) :=
    (outerMass_smooth f₀ hf₀ m hR).contDiffAt (positiveChart_open.mem_nhds hy)
  have hv (y : PhysicalPoint) (hy : 0<y 0) :=
    (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hpx : 0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) x :=
    sphericalMap_radicand f₀ m R hx ▸ hp
  have hreg : ∀ᶠ y in 𝓝 x, 0<y 0 ∧ Real.sin (y 1)≠0 ∧
      0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) y := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually (isOpen_Ioi.mem_nhds hx),
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs,
      (contDiffAt_radicand (hF x hx) (hv x hx) hx.ne').continuousAt.eventually (isOpen_Ioi.mem_nhds hpx)]
      with y hy hsy hpy
    exact ⟨hy,hsy,hpy⟩
  have hEqG : coordinatePullback sphericalMap (physicalMetric f₀ m R) =ᶠ[𝓝 x]
      outerMetric (outerMass f₀ m R) (bendingV R) := by
    filter_upwards [hreg] with y hy
    exact spherical_metric_pullback f₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  have hEqK : coordinatePullback sphericalMap (physicalTensor f₀ m R) =ᶠ[𝓝 x]
      outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R) (outerA f₀ R) (outerPhi f₀ R) := by
    filter_upwards [hreg] with y hy
    exact spherical_tensor_pullback f₀ hf₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  let frame : LocalFrame := fun i y => adaptedFrame
    (lapse (outerMass f₀ m R) (bendingV R) y) (y 0^2 • sphericalAngularMetric y) 0 i
  have hFrame : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt
      (coordinatePullback sphericalMap (physicalMetric f₀ m R)) frame y := by
    filter_upwards [hreg,hEqG.eventually_nhds] with y hy heq
    exact (round_smoothOrthonormalAt (hF y hy.1) (hv y hy.1) hy.1.ne' hy.2.1 hy.2.2).congr_metric heq
  have ha := (outerA_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hb := (outerPhi_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hK := (outerTensor_contDiffAt (hF x hx) (hv x hx) (bendingBeta_smooth R).contDiffAt ha hb hx.ne' hpx).congr_of_eventuallyEq hEqK
  have hsymm : (coordinatePullback sphericalMap (physicalTensor f₀ m R) x).IsHermitian := by
    rw [hEqK.self_of_nhds]
    exact CKSRealizedRound.tensor_hermitian ..
  have h := local_coordinate_DEC_pushforward (sphericalChart x hx.ne' hs)
    (physicalMetric f₀ m R) (physicalTensor f₀ m R) frame
    (sphericalChart_mem x hx.ne' hs) (Eventually.of_forall fun y => sphericalMap_smooth.contDiffAt)
    (sphericalChart_inverse_smooth x hx.ne' hs) hFrame hK hsymm
  change CKSLocalBending.DEC (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x))
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) ↔
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback sphericalMap (physicalMetric f₀ m R)) x)
      (physicalTensorJet (coordinatePullback sphericalMap (physicalTensor f₀ m R)) x) at h
  rw [physicalMetricJet_congr hEqG,physicalTensorJet_congr hEqK] at h
  exact h
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem sphericalMap_surjective_radial (y : E) :
    ∃ x : PhysicalPoint, x 0=‖y‖ ∧ sphericalMap x=toPoint y := by
  let z : ℂ := ⟨y 0,y 1⟩
  let w : ℂ := ⟨y 2,‖z‖⟩
  have hw : ‖w‖=‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
    change y 2*y 2+‖z‖*‖z‖=∑ i,y i^2
    rw [←pow_two ‖z‖,Complex.sq_norm,Complex.normSq_apply]
    simp only [z,Fin.sum_univ_three]
    ring
  have hs : ‖y‖*Real.sin w.arg=‖z‖ := by
    rw [←hw]
    exact Complex.norm_mul_sin_arg w
  have hc : ‖y‖*Real.cos w.arg=y 2 := by
    rw [←hw]
    exact Complex.norm_mul_cos_arg w
  have hz0 : ‖z‖*Real.cos z.arg=y 0 := Complex.norm_mul_cos_arg z
  have hz1 : ‖z‖*Real.sin z.arg=y 1 := Complex.norm_mul_sin_arg z
  refine ⟨![‖y‖,w.arg,z.arg],rfl,?_⟩
  apply toPoint.symm.injective
  rw [toPoint.symm_apply_apply]
  change (‖y‖ • sphereParam ![‖y‖,w.arg,z.arg] : E)=y
  ext i
  fin_cases i
  · change ‖y‖*(Real.sin w.arg*Real.cos z.arg)=y 0
    rw [←mul_assoc,hs,hz0]
  · change ‖y‖*(Real.sin w.arg*Real.sin z.arg)=y 1
    rw [←mul_assoc,hs,hz1]
  · change ‖y‖*Real.cos w.arg=y 2
    exact hc
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
structure ContinuousMetricJetAt (g : PhysicalPoint → CKSRound.MetricJet) (x : PhysicalPoint) : Prop where
  inv : ∀ i j, ContinuousAt (fun y => (g y).inv i j) x
  d : ∀ a i j, ContinuousAt (fun y => (g y).d a i j) x
  dd : ∀ a b i j, ContinuousAt (fun y => (g y).dd a b i j) x
structure ContinuousTensorJetAt (k : PhysicalPoint → CKSRound.TensorJet) (x : PhysicalPoint) : Prop where
  val : ∀ i j, ContinuousAt (fun y => (k y).val i j) x
  d : ∀ a i j, ContinuousAt (fun y => (k y).d a i j) x
lemma ContinuousMetricJetAt.gamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).gamma a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.gamma
  fun_prop
lemma ContinuousMetricJetAt.dInv {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).dInv a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.dInv
  fun_prop
lemma ContinuousMetricJetAt.dGamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a b i j : Fin 3) :
    ContinuousAt (fun y => (g y).dGamma a b i j) x := by
  have hi := h.inv
  have hd := h.d
  have hdd := h.dd
  have hdi := h.dInv
  unfold CKSRound.MetricJet.dGamma
  fun_prop
lemma ContinuousMetricJetAt.ricci {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (i j : Fin 3) :
    ContinuousAt (fun y => (g y).ricci i j) x := by
  have hc := h.gamma
  have hd := h.dGamma
  unfold CKSRound.MetricJet.ricci
  fun_prop
lemma ContinuousMetricJetAt.scalar {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) : ContinuousAt (fun y => (g y).scalar) x := by
  have hi := h.inv
  have hr := h.ricci
  unfold CKSRound.MetricJet.scalar
  fun_prop
lemma ContinuousMetricJetAt.trace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).trace (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.trace
  fun_prop
lemma ContinuousMetricJetAt.normSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).normSq (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.normSq
  fun_prop
lemma ContinuousMetricJetAt.dTrace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).dTrace (k y) i) x := by
  have hi := h.inv
  have hdi := h.dInv
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.dTrace
  fun_prop
lemma ContinuousMetricJetAt.tensorDivergence {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).tensorDivergence (k y) i) x := by
  have hi := h.inv
  have hc := h.gamma
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.tensorDivergence
  fun_prop
lemma ContinuousMetricJetAt.energy {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).energy (k y)) x := by
  have hs := h.scalar
  have ht := h.trace hk
  have hn := h.normSq hk
  unfold CKSRound.MetricJet.energy
  fun_prop
lemma ContinuousMetricJetAt.momentum {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).momentum (k y) i) x := by
  have ht := h.dTrace hk i
  have hd := h.tensorDivergence hk i
  unfold CKSRound.MetricJet.momentum
  fun_prop
lemma ContinuousMetricJetAt.momentumSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => CKSLocalBending.momentumSq (g y) (k y)) x := by
  have hi := h.inv
  have hm := h.momentum hk
  unfold CKSLocalBending.momentumSq
  fun_prop
lemma physicalMetricJet_continuousAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) : ContinuousMetricJetAt (physicalMetricJet G) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  refine ⟨fun i j => (matrix_inv_component_contDiffAt hg h0 i j).continuousAt,?_,?_⟩
  · intro a i j
    exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
  · intro a b i j
    exact (contDiffAt_D (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis b))
      (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
lemma physicalTensorJet_continuousAt {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hk : ContDiffAt ℝ ∞ K x) : ContinuousTensorJetAt (physicalTensorJet K) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  refine ⟨fun i j => (hc i j).continuousAt,?_⟩
  intro a i j
  exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
theorem physical_DEC_closed_along {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x) (h0 : (G x).det ≠ 0)
    {u : ℕ → PhysicalPoint} (hu : Tendsto u atTop (𝓝 x))
    (hdec : ∀ᶠ n in atTop, CKSLocalBending.DEC (physicalMetricJet G (u n)) (physicalTensorJet K (u n))) :
    CKSLocalBending.DEC (physicalMetricJet G x) (physicalTensorJet K x) := by
  have hgj := physicalMetricJet_continuousAt hg h0
  have hkj := physicalTensorJet_continuousAt hk
  have he := (hgj.energy hkj).tendsto.comp hu
  have hm := ((hgj.momentumSq hkj).sqrt).tendsto.comp hu
  exact le_of_tendsto_of_tendsto hm he hdec
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma regular_angular_approximation (x : PhysicalPoint) (hs : Real.sin (x 1)=0) :
    ∃ u : ℕ → PhysicalPoint, Tendsto u atTop (𝓝 x) ∧
      ∀ n, u n 0=x 0 ∧ Real.sin (u n 1)≠0 := by
  have hc : Real.cos (x 1)≠0 := by
    intro hh
    have h := Real.sin_sq_add_cos_sq (x 1)
    simp [hs,hh] at h
  let u : ℕ → PhysicalPoint := fun n => ![x 0,x 1+1/((n:ℝ)+1),x 2]
  refine ⟨u,?_,?_⟩
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · simpa [u] using
        (tendsto_const_nhds (x := x 1)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact tendsto_const_nhds
  · intro n
    refine ⟨rfl,?_⟩
    change Real.sin (x 1+1/((n:ℝ)+1))≠0
    rw [Real.sin_add,hs,zero_mul,zero_add]
    apply mul_ne_zero hc
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    have hle : (1:ℝ)/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith [Real.pi_gt_three]
lemma spherical_DEC_extend_poles {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G (sphericalMap x)) (hk : ContDiffAt ℝ ∞ K (sphericalMap x))
    (h0 : (G (sphericalMap x)).det≠0)
    (hdec : ∀ p : PhysicalPoint, p 0=x 0 → Real.sin (p 1)≠0 →
      CKSLocalBending.DEC (physicalMetricJet G (sphericalMap p)) (physicalTensorJet K (sphericalMap p))) :
    CKSLocalBending.DEC (physicalMetricJet G (sphericalMap x)) (physicalTensorJet K (sphericalMap x)) := by
  by_cases hs : Real.sin (x 1)≠0
  · exact hdec x rfl hs
  · obtain ⟨u,hu,hreg⟩ := regular_angular_approximation x (not_ne_iff.mp hs)
    exact physical_DEC_closed_along hg hk h0 (sphericalMap_smooth.continuous.continuousAt.tendsto.comp hu)
      (Eventually.of_forall fun n => hdec (u n) (hreg n).1 (hreg n).2)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem constructed_cartesian_outer_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
    CKSLocalBending.DEC (physicalMetricJet (physicalMetric f₀ m R) (toPoint x))
      (physicalTensorJet (physicalTensor f₀ m R) (toPoint x)) := by
  obtain ⟨R₁,hR₁,hpos⟩ := cartesian_radicand_positive f₀ hf₀ m
  obtain ⟨R₂,hR₂,hdec⟩ := constructed_outer_DEC f₀ hf₀ m
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),?_⟩
  intro R hR y hy
  have hRR₁ : R₁≤R := (le_max_left _ _).trans hR
  have hRR₂ : R₂≤R := (le_max_right _ _).trans hR
  have hR12 : 12≤R := hR₁.trans hRR₁
  have hRp : 0<R := by linarith
  have hyp : y≠0 := norm_pos_iff.mp (by linarith : 0<‖y‖)
  obtain ⟨x,hxr,hx⟩ := sphericalMap_surjective_radial y
  have hpx := hpos R hRR₁ y hy
  have hg : ContDiffAt ℝ ∞ (physicalMetric f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (metric_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  have hk : ContDiffAt ℝ ∞ (physicalTensor f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (tensor_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  rw [←hx]
  apply spherical_DEC_extend_poles hg hk
  · change (metric f₀ m R (toPoint.symm (sphericalMap x))).det≠0
    rw [hx,toPoint.symm_apply_apply]
    exact (metric_positive hyp hpx).det_pos.ne'
  · intro p hpr hs
    have hpr' : 0<p 0 := by rw [hpr,hxr]; linarith
    have hprR : 3*R≤p 0 := by rw [hpr,hxr]; exact hy
    have hp := hpos R hRR₁ (toPoint.symm (sphericalMap p)) (by rwa [sphericalMap_norm hpr'])
    exact (spherical_physical_DEC_iff f₀ hf₀ m hRp hpr' hs hp).mpr (hdec R hRR₂ p hprR hs)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSBending
noncomputable section
open Set
open scoped Topology ContDiff

lemma constant_halfline_full_jets {f : ℝ → ℝ} {c x : ℝ} (hf : ContDiffAt ℝ ∞ f x)
    {S : Set ℝ} (hS : UniqueDiffOn ℝ S) (hx : x ∈ S) (he : EqOn f (fun _ => c) S) (n : ℕ) :
    iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n (fun _ : ℝ => c) x := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hS
    (hf.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n:ℕ∞) ≤ ⊤))) hx,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hS (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => c) x) hx]
  exact iteratedFDerivWithin_congr he hx n

lemma roundingWeight_flat_initial {R r : ℝ} (hR : 0<R) (hr : r ≤ 2*R) (n : ℕ) :
    iteratedFDeriv ℝ n (roundingWeight R) r=iteratedFDeriv ℝ n (fun _ : ℝ => 0) r :=
  constant_halfline_full_jets (roundingWeight_smooth R).contDiffAt (uniqueDiffOn_Iic (2*R)) hr
    (fun _ h => roundingWeight_zero hR h) n

lemma roundingWeight_flat_final {R r : ℝ} (hR : 0<R) (hr : 3*R ≤ r) (n : ℕ) :
    iteratedFDeriv ℝ n (roundingWeight R) r=iteratedFDeriv ℝ n (fun _ : ℝ => 1) r :=
  constant_halfline_full_jets (roundingWeight_smooth R).contDiffAt (uniqueDiffOn_Ici (3*R)) hr
    (fun _ h => roundingWeight_one hR h) n

lemma paddingWeight_flat_initial {R r : ℝ} (hR : 0<R) (hr : r ≤ R) (n : ℕ) :
    iteratedFDeriv ℝ n (paddingWeight R) r=iteratedFDeriv ℝ n (fun _ : ℝ => 0) r :=
  constant_halfline_full_jets (paddingWeight_smooth R).contDiffAt (uniqueDiffOn_Iic R) hr
    (fun _ h => paddingWeight_zero hR h) n

lemma paddingWeight_flat_final {R r : ℝ} (hR : 0<R) (hr : 2*R ≤ r) (n : ℕ) :
    iteratedFDeriv ℝ n (paddingWeight R) r=iteratedFDeriv ℝ n (fun _ : ℝ => 1) r :=
  constant_halfline_full_jets (paddingWeight_smooth R).contDiffAt (uniqueDiffOn_Ici (2*R)) hr
    (fun _ h => paddingWeight_one hR h) n

lemma paddingMass_flat_initial {R r : ℝ} (hR : 0<R) (hr : r ≤ R) (hp : 0<r) (n : ℕ) :
    iteratedFDeriv ℝ n (paddingMass R) r=iteratedFDeriv ℝ n (fun _ : ℝ => 0) r :=
  constant_halfline_full_jets ((paddingMass_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hp))
    (uniqueDiffOn_Iic R) hr (fun _ h => paddingMass_initial hR h) n

lemma roundingWeight_deriv_final {R r : ℝ} (hR : 0<R) (hr : 3*R ≤ r) :
    deriv (roundingWeight R) r=0 := by
  have hm : IsLocalMax (roundingWeight R) r := by
    apply Filter.Eventually.of_forall
    intro y
    rw [roundingWeight_one hR hr]
    exact roundingWeight_le_one R y
  exact hm.deriv_eq_zero
end
end CKSBending

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSBending Set
open scoped ContDiff

lemma collar_fields_initial {R : ℝ} (hR : 0<R) (f : LogCollarData) {y : MP}
    (hy : Real.exp (y 0) ≤ R) :
    collarQ R f y=f.sigma y+f.metricError y ∧
    collarShift R f y=f.shift y ∧ collarT R f y=1+f.tError y ∧
    collarLb R f y=1+f.LError y ∧ collarL R f y=1+f.LError y ∧
    collarF R f y=f.fstar y+f.massError y ∧ collarEtaDivR R f y=f.etaDivR y := by
  have he := roundingWeight_zero hR (hy.trans (by linarith : R ≤ 2*R))
  have hw := paddingWeight_zero hR hy
  have hc := paddingMass_initial hR hy
  simp [collarQ,collarShift,collarT,collarLb,collarL,collarF,collarEtaDivR,radialLift,he,hw,hc]

lemma collar_fields_final {R : ℝ} (hR : 0<R) (f : LogCollarData) {y : MP}
    (hy : 3*R ≤ Real.exp (y 0)) :
    collarQ R f y=f.sigma y ∧ collarShift R f y=0 ∧ collarT R f y=1 ∧
    collarLb R f y=1 ∧ collarL R f y=1+1/Real.exp (y 0)^2 ∧
    collarF R f y=f.fstar y+paddingMass R (Real.exp (y 0)) ∧ collarEtaDivR R f y=0 := by
  have he := roundingWeight_one hR hy
  have hw := paddingWeight_one hR ((by linarith : 2*R ≤ 3*R).trans hy)
  simp [collarQ,collarShift,collarT,collarLb,collarL,collarF,collarEtaDivR,radialLift,he,hw]

lemma collarQ_positive {R : ℝ} (f : LogCollarData) (y : MP)
    (hσ : (f.sigma y).PosDef) (h0 : (f.sigma y+f.metricError y).PosDef) :
    (collarQ R f y).PosDef := by
  have he : collarQ R f y=(1-roundingWeight R (Real.exp (y 0))) •
      (f.sigma y+f.metricError y)+roundingWeight R (Real.exp (y 0)) • f.sigma y := by
    ext a b
    simp only [collarQ,radialLift,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact CKSAngularGeometry.convex_metric_posDef h0 hσ
    (roundingWeight_nonneg _ _) (roundingWeight_le_one _ _)

end
end CKSAngularSlice

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Matrix Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma round_leafRadialRate (x : CKSRealizedRound.Point) :
    leafRadialRate (fun y => y 0^2 • sphericalAngularMetric y) (fun _ => 0) x =
      (2*x 0) • sphericalAngularMetric x := by
  have hD (a b : Fin 2) :
      D (CKSRealizedRound.basis 0) (fun y : CKSRealizedRound.Point =>
        (y 0^2 • sphericalAngularMetric y) a b) x =
        2*x 0*sphericalAngularMetric x a b := by
    fin_cases a <;> fin_cases b
    · change D (CKSRealizedRound.basis 0) (fun y => y 0^2*1) x = 2*x 0*1
      simpa using D_r_sq 0 x
    · simp [sphericalAngularMetric,D_const]
    · simp [sphericalAngularMetric,D_const]
    · change D (CKSRealizedRound.basis 0) (fun y => y 0^2*Real.sin (y 1)^2) x =
        2*x 0*Real.sin (x 1)^2
      rw [D_mul (CKSRealizedRound.basis 0) (by fun_prop) (by fun_prop),D_r_sq,D_sin_sq]
      simp
      ring
  ext a b
  simp only [leafRadialRate,Pi.zero_apply,D_const,zero_mul,mul_zero,add_zero,
    Finset.sum_const_zero,sub_zero,Matrix.smul_apply,smul_eq_mul]
  exact hD a b

lemma round_radialExpansion {x : CKSRealizedRound.Point}
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    radialExpansion (fun y => y 0^2 • sphericalAngularMetric y) (fun _ => 0) x=1 := by
  have hscale : (2*x 0) • sphericalAngularMetric x =
      (2/x 0) • (x 0^2 • sphericalAngularMetric x) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [radialExpansion,round_leafRadialRate,hscale,leafTensorTrace_smul,
    leafTensorTrace_self (roundAngularMetric_posDef hr hs)]
  field_simp
  ring

lemma final_collar_fields {R : ℝ} {f : LogCollarData} {x : CKSRealizedRound.Point}
    (hR : 0 < R) (hr : 3*R ≤ x 0) :
    physicalCollarGamma R f x=x 0^2 • f.sigma (radiusLogPoint x) ∧
    physicalCollarShift R f x=0 ∧ physicalCollarT R f x=1 ∧
    physicalCollarF R f x=f.fstar (radiusLogPoint x)+paddingMass R (x 0) ∧
    physicalCollarL R f x=1+1/x 0^2 ∧ physicalCollarEta R f x=0 ∧
    physicalCollarRawTau R f x=0 := by
  have hrp : 0 < x 0 := by linarith
  have h := collar_fields_final hR f (y := radiusLogPoint x) (by simpa [radiusLogPoint_exp hrp] using hr)
  simp only [radiusLogPoint_exp hrp] at h
  refine ⟨?_,h.2.1,h.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · exact congrArg (fun q => x 0^2 • q) h.1
  · unfold physicalCollarEta
    rw [h.2.2.2.2.2.2,smul_zero]
  · simp only [physicalCollarRawTau,roundingWeight_one hR hr,sub_self,mul_zero,zero_smul]

lemma final_collar_radialExpansion {R : ℝ} {f : LogCollarData} {x : CKSRealizedRound.Point}
    (hR : 0 < R) (hr : 3*R < x 0) (hs : Real.sin (x 1) ≠ 0)
    (hσ : ∀ᶠ y in 𝓝 x, f.sigma (radiusLogPoint y)=sphericalAngularMetric y) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x=1 := by
  have hn := (coord 0).continuous.continuousAt.eventually (Ioi_mem_nhds hr)
  have hfields : ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R f y=y 0^2 • sphericalAngularMetric y ∧ physicalCollarShift R f y=0 := by
    filter_upwards [hn,hσ] with y hyr hyσ
    obtain ⟨hγ,hshift,-⟩ := final_collar_fields (f := f) hR hyr.le
    exact ⟨by rw [hγ,hyσ],hshift⟩
  rw [radialExpansion_congr (hfields.mono (fun _ h => h.1))
    (hfields.mono (fun _ h => h.2))]
  exact round_radialExpansion (by linarith) hs

lemma bendingV_deriv_initial {R r : ℝ} (hR : 12 ≤ R) (hr : r < 6*R) :
    deriv (bendingV R) r=1 := by
  have h : bendingV R =ᶠ[𝓝 r] (fun s : ℝ => s) := by
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact bendingV_initial hR hs.le
  rw [h.deriv_eq]
  simp

end
end CKSSphericalChart

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem physical_collar_outer_overlap {R : ℝ} (hR : 12 ≤ R)
    (f : LogCollarData) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    (hbal : Balanced f₀ m) {x : CKSRealizedRound.Point}
    (hr : 3*R < x 0) (hr' : x 0 < (7/2)*R) (hs : Real.sin (x 1) ≠ 0)
    (hσ : ∀ᶠ y in 𝓝 x, f.sigma (radiusLogPoint y)=sphericalAngularMetric y)
    (hf : f.fstar (radiusLogPoint x)=
      f₀ ⟨sphereParam x,by simpa only [Metric.mem_sphere,dist_zero_right] using sphereParam_norm x⟩) :
    physicalCollarMetric R f x = outerMetric (outerMass f₀ m R) (bendingV R) x ∧
    physicalCollarTensor R f x = outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R)
      (outerA f₀ R) (outerPhi f₀ R) x ∧
    ∀ i, physicalCollarFrame R f i x = adaptedFrame
      (lapse (outerMass f₀ m R) (bendingV R) x)
      (x 0^2 • sphericalAngularMetric x) 0 i
 := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  have hv := bendingV_initial hR (by linarith : x 0 ≤ 6*R)
  have hdv := bendingV_deriv_initial hR (by linarith : x 0 < 6*R)
  have hβ : bendingBeta R (x 0)=1 :=
    beta_one_near ((div_le_iff₀ hRp).mpr hr'.le)
  have hcor : correctionCoeff (bendingV R) (x 0)=0 := by
    simp [correctionCoeff,hv,hdv,hrp.ne']
  obtain ⟨hγ,hs',ht,hF,hL,hη,hτ⟩ := final_collar_fields (f := f) hRp hr.le
  rw [hσ.self_of_nhds] at hγ
  have hFm : physicalCollarF R f x=outerMass f₀ m R x := by
    rw [hF,hf,constructed_outer_mass_initial f₀ hf₀ m hbal hRp (by linarith)]
    ring
  have hU : physicalCollarU R f x=lapse (outerMass f₀ m R) (bendingV R) x := by
    unfold physicalCollarU radialMassLapse
    rw [final_collar_radialExpansion hRp hr hs hσ]
    simp only [radialMassRadical,ht,hFm,div_one,mul_one,lapse,radicand,radial,hv]
  have hT : physicalCollarTangential R f x=x 0^2 • sphericalAngularMetric x := by
    simp [physicalCollarTangential,radialTangential,ht,hγ,hτ,leafTensorTraceFree,leafTensorTrace]
  refine ⟨?_,?_,?_⟩
  · rw [physicalCollarMetric,hU,hγ,hs',outerMetric_foliation]
  · rw [physicalCollarTensor,hU,hL,hη,hT,hs']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [foliationTensor,metricBlock,outerTensor,tensor,radial,normalEntry,
        correctedComponent,hcor,hv,hdv,hβ,sphericalAngularMetric,Matrix.smul_apply,
    Matrix.of_apply,pow_two]
  · intro i
    simp only [physicalCollarFrame,hU,hγ,hs']

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients

def spatialMatrix (F : E → AmbientMat) : SpatialTensor := fun x =>
  (matrixBilinear (F x)).bilinearComp (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma angular_round_leafRadialRate (P : SmoothAngularPatch) {x : CKSMixedGeometry.Point}
    (hx : angularProjection x ∈ P.chart.target) :
    leafRadialRate (fun y => y 0^2 • angularRoundMetric P.param (angularProjection y)) (fun _ => 0) x =
      (2*x 0) • angularRoundMetric P.param (angularProjection x) := by
  have hσ := P.roundMetric_contDiffAt hx
  have hD (a b : Fin 2) :
      D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) a b) x =
        2*x 0*angularRoundMetric P.param (angularProjection x) a b := by
    have ha := (contDiffAt_pi.mp (contDiffAt_pi.mp hσ a) b).differentiableAt (by simp)
    change D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
      y 0^2 * (angularLift (fun θ => angularRoundMetric P.param θ a b)) y) x = _
    have hp := D_mul (CKSRealizedRound.basis 0)
      (show DifferentiableAt ℝ (fun y : CKSMixedGeometry.Point => y 0^2) x by fun_prop)
      (ha.comp x angularProjection.differentiableAt)
    change D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
      y 0^2 * (angularLift (fun θ => angularRoundMetric P.param θ a b)) y) x = _ at hp
    rw [hp]
    have haD : D (CKSRealizedRound.basis 0)
        ((fun θ => angularRoundMetric P.param θ a b) ∘ angularProjection) x = 0 := D_angularLift ha
    rw [haD,CKSRealizedRound.D_r_sq]
    simp only [mul_zero,zero_add,Fin.isValue,Matrix.cons_val_zero,Function.comp_apply]
    ring
  ext a b
  simp only [leafRadialRate,Pi.zero_apply,D_const,zero_mul,mul_zero,add_zero,
    Finset.sum_const_zero,sub_zero,Matrix.smul_apply,smul_eq_mul]
  exact hD a b
lemma angular_round_radialExpansion (P : SmoothAngularPatch) {x : CKSMixedGeometry.Point}
    (hr : x 0 ≠ 0) (hx : angularProjection x ∈ P.chart.target) :
    radialExpansion (fun y => y 0^2 • angularRoundMetric P.param (angularProjection y)) (fun _ => 0) x=1 := by
  have hscale : (2*x 0) • angularRoundMetric P.param (angularProjection x) =
      (2/x 0) • (x 0^2 • angularRoundMetric P.param (angularProjection x)) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [radialExpansion,angular_round_leafRadialRate P hx,hscale,leafTensorTrace_smul,
    leafTensorTrace_self ((P.roundMetric_posDef hx).smul (sq_pos_of_ne_zero hr))]
  field_simp
  ring
lemma final_angular_collar_radialExpansion (P : SmoothAngularPatch) {R : ℝ}
    {f : LogCollarData} {x : CKSMixedGeometry.Point} (hR : 0 < R) (hr : 3*R < x 0)
    (hx : angularProjection x ∈ P.chart.target)
    (hσ : ∀ᶠ y in 𝓝 x, f.sigma (radiusLogPoint y)=angularRoundMetric P.param (angularProjection y)) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x=1 := by
  have hn : ∀ᶠ z in 𝓝 x, 3*R < z 0 :=
    (show ContinuousAt (fun z : CKSMixedGeometry.Point => z 0) x from (continuous_apply 0).continuousAt).eventually (Ioi_mem_nhds hr)
  have hfields : ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R f y=y 0^2 • angularRoundMetric P.param (angularProjection y) ∧
      physicalCollarShift R f y=0 := by
    filter_upwards [hn,hσ] with y hyr hyσ
    obtain ⟨hγ,hs,-⟩ := CKSSphericalChart.final_collar_fields (f := f) hR hyr.le
    exact ⟨by rw [hγ,hyσ],hs⟩
  rw [radialExpansion_congr (hfields.mono (fun _ h => h.1)) (hfields.mono (fun _ h => h.2))]
  exact angular_round_radialExpansion P (by linarith) hx
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients CKSCartesianOuter CKSInducedSphere CKSSphericalChart
open scoped BigOperators
lemma spatialMatrix_apply (F : E → AmbientMat) (x v w : E) :
    spatialMatrix F x v w = pair (F x) v w := by
  have hh := matrixBilinear_apply (fun i j => F x i j) (fun i => v i) (fun i => w i)
  change spatialMatrix F x v w = _ at hh
  rw [hh]
  simp only [pair,Fin.sum_univ_three]
  ring
lemma euclidean_inner_sum (v w : E) : inner ℝ v w = ∑ i : Fin 3, v i*w i := by
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]
lemma spatialMatrix_radial (a b : ℝ) (n v w : E) :
    pair (b • (1 : AmbientMat) + (a-b) • Matrix.vecMulVec (fun i => n i) (fun i => n i)) v w =
      b * inner ℝ v w + (a-b)*inner ℝ n v*inner ℝ n w := by
  rw [pair_add_matrix,pair_smul_matrix,pair_smul_matrix,pair_one,pair_rankOne]
  simp only [euclidean_inner_sum]
  ring
lemma normal_polarParam (P : SmoothAngularPatch) {y : CKSMixedGeometry.Point} (hr : 0 < y 0) :
    CKSADM.normal (polarParam P y) = fun i => P.param (angularProjection y) i := by
  funext i
  rw [CKSADM.normal,polarParam_norm P hr.le]
  change (y 0 * P.param (angularProjection y) i) / y 0 = _
  field_simp
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
open scoped Matrix.Norms.Elementwise
lemma radial_matrix_polar (P : SmoothAngularPatch) (F : E → AmbientMat) (a b : ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : F (polarParam P y) = b • (1:AmbientMat) + (a-b) •
      Matrix.vecMulVec (CKSADM.normal (polarParam P y)) (CKSADM.normal (polarParam P y))) :
    (fun i j => polarTensorComponents P (spatialMatrix F) i j y) =
      CKSAngularGeometry.metricBlock a 0 ((b*(y 0)^2) • angularRoundMetric P.param (angularProjection y)) := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  have happ (i j : Fin 3) : polarTensorComponents P (spatialMatrix F) i j y =
      b * inner ℝ (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis i))
        (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis j)) +
      (a-b) * inner ℝ (P.param (angularProjection y)) (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis i)) *
        inner ℝ (P.param (angularProjection y)) (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis j)) := by
    change spatialMatrix F (polarParam P y) _ _ = _
    rw [spatialMatrix_apply,hF,normal_polarParam P hr,spatialMatrix_radial]
  ext i j
  rw [happ]
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · rw [polarParam_fderiv_radial P hy,hi]
      simp [CKSAngularGeometry.metricBlock]
    · rw [polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases d <;> simp [CKSAngularGeometry.metricBlock,real_inner_smul_right,ht]
  · refine Fin.cases ?_ (fun d => ?_) j
    · rw [polarParam_fderiv_angular P hy,polarParam_fderiv_radial P hy]
      have htc : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis c)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases c <;> simp_all [CKSAngularGeometry.metricBlock,real_inner_smul_left,real_inner_smul_right]
    · rw [polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [real_inner_smul_left,real_inner_smul_right,ht,mul_zero,add_zero]
      fin_cases c <;> fin_cases d <;>
        simp [CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSADM CKSBending CKSSphericalHarmonics CKSInducedSphere
open CKSRealizedRound (correctionCoeff)
open scoped Matrix.Norms.Elementwise
lemma cartMass_polar_initial (P : SmoothAngularPatch) (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m) {R : ℝ} (hR : 0 < R)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (ht : y 0 ≤ 4*R) :
    cartMass f₀ m R (polarParam P y) = paddingMass R (y 0) + f₀ (P.chart.symm (angularProjection y)) := by
  rw [cartMass,polarParam_norm P hr.le,heatTime_initial hR ht]
  have hu : unitVector (polarParam P y) = (P.chart.symm (angularProjection y) : E) :=
    unitVector_radius hr (P.chart.symm (angularProjection y))
  rw [hu]
  congr 1
  exact canonicalF_initial f₀ hf₀ m hbal _
lemma outer_tensor_initial_matrix (f₀ : C(Sphere,ℝ)) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) {x : E} (hr : 0 < ‖x‖) (ht : ‖x‖ < (7/2)*R) :
    CKSCartesianOuter.tensor f₀ m R x =
      (1 : AmbientMat) + ((1+1/‖x‖^2)/CKSCartesianOuter.radicand f₀ m R x-1) •
        Matrix.vecMulVec (normal x) (normal x) := by
  have hRp : 0 < R := by linarith
  have hv := bendingV_initial hR (by linarith : ‖x‖ ≤ 6*R)
  have hdv := bendingV_deriv_initial hR (by linarith : ‖x‖ < 6*R)
  have hβ : bendingBeta R ‖x‖=1 := beta_one_near ((div_le_iff₀ hRp).mpr ht.le)
  have hcor : correctionCoeff (bendingV R) ‖x‖=0 := by
    simp [correctionCoeff,hv,hdv,hr.ne']
  rw [CKSCartesianOuter.tensor,hcor,hv]
  simp only [zero_div,zero_smul,add_zero,div_self hr.ne',one_smul]
  unfold CKSRealizedRound.normalEntry
  rw [hdv,hβ]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSSphericalHarmonics CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma collar_outer_blocks (P : SmoothAngularPatch) (f : LogCollarData)
    (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m)
    {R : ℝ} (hR : 12 ≤ R) {y : CKSMixedGeometry.Point}
    (hr : 3*R < y 0) (hr' : y 0 < (7/2)*R) (hy : angularProjection y ∈ P.chart.target)
    (hσ : ∀ᶠ z in 𝓝 y, f.sigma (radiusLogPoint z)=angularRoundMetric P.param (angularProjection z))
    (hf : f.fstar (radiusLogPoint y)=f₀ (P.chart.symm (angularProjection y)))
    (hp : 0 < CKSCartesianOuter.radicand f₀ m R (polarParam P y)) :
    physicalCollarMetric R f y = metricBlock
      (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
      ((y 0)^2 • angularRoundMetric P.param (angularProjection y)) ∧
    physicalCollarTensor R f y = metricBlock
      ((1+1/(y 0)^2)/CKSCartesianOuter.radicand f₀ m R (polarParam P y)) 0
      ((y 0)^2 • angularRoundMetric P.param (angularProjection y)) := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hv := bendingV_initial hR (by linarith : y 0 ≤ 6*R)
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := final_collar_fields (f := f) hRp hr.le
  rw [hσ.self_of_nhds] at hγ
  have hFm : physicalCollarF R f y = CKSADM.cartMass f₀ m R (polarParam P y) := by
    rw [hF,hf,cartMass_polar_initial P f₀ hf₀ m hbal hRp hrp (by linarith)]
    ring
  have hU : physicalCollarU R f y = Real.sqrt (CKSCartesianOuter.radicand f₀ m R (polarParam P y)) := by
    rw [physicalCollarU,radialMassLapse,final_angular_collar_radialExpansion P hRp hr hy hσ]
    simp only [div_one,radialMassRadical,ht,hFm,mul_one,CKSCartesianOuter.radicand,
      polarParam_norm P hrp.le,hv]
  have hU2 : (physicalCollarU R f y)^2=CKSCartesianOuter.radicand f₀ m R (polarParam P y) := by
    rw [hU,Real.sq_sqrt hp.le]
  have hT : physicalCollarTangential R f y=y 0^2 • angularRoundMetric P.param (angularProjection y) := by
    simp [physicalCollarTangential,radialTangential,ht,hγ,hτ,leafTensorTraceFree,leafTensorTrace]
  constructor
  · simp only [physicalCollarMetric,foliationMetric,hU2,hγ,hs,one_div]
    simp
    rfl
  · simp [physicalCollarTensor,foliationTensor,hU2,hL,hη,hT,hs]
    rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Filter
open scoped Topology ContDiff

theorem physical_collar_outer_spatial_overlap (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ (P : SmoothAngularPatch) (f : LogCollarData)
      (y : CKSMixedGeometry.Point), 3*R < y 0 → y 0 < (7/2)*R →
      angularProjection y ∈ P.chart.target →
      (∀ᶠ z in 𝓝 y, f.sigma (radiusLogPoint z) = angularRoundMetric P.param (angularProjection z)) →
      f.fstar (radiusLogPoint y) = f₀ (P.chart.symm (angularProjection y)) →
      polarLift P (physicalCollarMetric R f) (polarParam P y) =
        spatialMatrix (CKSCartesianOuter.metric f₀ m R) (polarParam P y) ∧
      polarLift P (physicalCollarTensor R f) (polarParam P y) =
        spatialMatrix (CKSCartesianOuter.tensor f₀ m R) (polarParam P y) := by
  obtain ⟨R₀,hR₀,hpos⟩ := CKSCartesianOuter.cartesian_radicand_positive f₀ hf₀ m
  refine ⟨R₀,hR₀,?_⟩
  intro R hR P f y hr ht hy hσ hf
  have h12 := hR₀.trans hR
  have hrp : 0 < y 0 := by linarith
  have hn := polarParam_norm P hrp.le
  have hp := hpos R hR (polarParam P y) (by rw [hn]; exact hr.le)
  have hb := collar_outer_blocks P f f₀ hf₀ m hbal h12 hr ht hy hσ hf hp
  constructor
  · apply (polarLift_reconstruction P (physicalCollarMetric R f) hrp hy).2
    have hlocal := radial_matrix_polar P (CKSCartesianOuter.metric f₀ m R)
      (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 1 hrp hy
      (by simp only [CKSCartesianOuter.metric,one_smul])
    simp only [one_mul] at hlocal
    intro i j
    exact congrArg (fun M : AmbientMat => M i j) (hlocal.trans hb.1.symm)
  · apply (polarLift_reconstruction P (physicalCollarTensor R f) hrp hy).2
    have hmat := outer_tensor_initial_matrix f₀ m h12
      (by rw [hn]; exact hrp) (by rw [hn]; exact ht)
    rw [hn] at hmat
    have hlocal := radial_matrix_polar P (CKSCartesianOuter.tensor f₀ m R)
      ((1+1/(y 0)^2)/CKSCartesianOuter.radicand f₀ m R (polarParam P y)) 1 hrp hy
      (by simpa only [one_smul] using hmat)
    simp only [one_mul] at hlocal
    intro i j
    exact congrArg (fun M : AmbientMat => M i j) (hlocal.trans hb.2.symm)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

def SourceCollarAtlas.HasMassAspect {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (M : Sphere → ℝ) : Prop :=
  ∀ i θ, θ ∈ (q.patch i).region →
    cksChartMassAspect (q.patch i).patch.param (q.patch i).mr
      (q.patch i).mg (q.patch i).mK θ = M ((q.patch i).patch.chart.symm θ)

def SourceCollarAtlas.replacementMetric {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m R : ℝ) : SpatialTensor := fun x =>
  if ‖x‖ ≤ R then sourceSpatial A x else
  if ‖x‖ ≤ 3*R then q.metric R x else spatialMatrix (CKSCartesianOuter.metric f₀ m R) x
def SourceCollarAtlas.replacementTensor {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m R : ℝ) : SpatialTensor := fun x =>
  if ‖x‖ ≤ R then sourceSpatial B x else
  if ‖x‖ ≤ 3*R then q.tensor R x else spatialMatrix (CKSCartesianOuter.tensor f₀ m R) x
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma CollarSourcePatch.aspect_eq {A B : SpatialTensor} (P : CollarSourcePatch A B) (θ : Angle) :
    sourceAspect P.fields.base θ = cksChartMassAspect P.patch.param P.mr P.mg P.mK θ := by
  unfold sourceAspect cksChartMassAspect angularMetricTrace
  rw [inverse_eq]
  simp only [CollarSourcePatch.fields,spatialSourceFields,cksSourceFields,CKSMixedGeometry.traceProduct,
    Matrix.trace,Matrix.diag]
  rfl
lemma SourceCollarAtlas.fstar_mass {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hm : q.HasMassAspect M) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ (q.patch i).region) :
    (sourceCollarData (q.patch i).fields.logFields).fstar (radiusLogPoint y) =
      heatDatum M hM ((q.patch i).patch.chart.symm (angularProjection y)) := by
  change cksLeadingField (q.patch i).fields.base.logFields (radiusLogPoint y) = _
  rw [source_leading_mass]
  change sourceAspect (q.patch i).fields.base (angularProjection y)/4 = _
  rw [(q.patch i).aspect_eq,hm i _ hy]
  rfl
lemma SourceCollarAtlas.eventually_outer_recovery {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hm : q.HasMassAspect M) (m : ℝ) (hc : bondiCharge M = (m,0)) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ i x,
      3*R < ‖x‖ → ‖x‖ < (7/2)*R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
      (q.patch i).metric R x = spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
      (q.patch i).tensor R x = spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x := by
  obtain ⟨R₀,hR₀,hrec⟩ := physical_collar_outer_spatial_overlap (heatDatum M hM)
    (heatDatum_smooth hM) m (heatDatum_balanced hM hc)
  refine ⟨R₀,hR₀,?_⟩
  intro R hR i x hr ht hx
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hx
  have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
  have hh := hrec R hR (q.patch i).patch (sourceCollarData (q.patch i).fields.logFields)
    (polarInverse (q.patch i).patch x) (by rwa [hyr]) (by rwa [hyr]) hyt
    (Eventually.of_forall (fun z => rfl)) (q.fstar_mass hM hm i hyw)
  rw [hyx] at hh
  exact hh
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.replacement_localization {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hm : q.HasMassAspect M) (m : ℝ) (hc : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧ ∀ R ≥ R₀,
      (∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
        PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
          (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y ∧
        physicalDEC (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
          (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
          (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y) ∧
      ∀ i x, R ≤ ‖x‖ → ‖x‖ ≤ 3*R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
        ∀ᶠ z in 𝓝 x,
          q.replacementMetric (heatDatum M hM) m R z = (q.patch i).metric R z ∧
          q.replacementTensor (heatDatum M hM) m R z = (q.patch i).tensor R z := by
  obtain ⟨S,hS,hqS,hinner⟩ := q.eventually_inner_recovery hA hB
  obtain ⟨R₁,hR₁,hq₁,hreg⟩ := q.eventually_pointwise
  obtain ⟨R₂,hR₂,houter⟩ := q.eventually_outer_recovery hM hm m hc
  let R₀ := max (max R₁ R₂) (S+1)
  refine ⟨S,R₀,hS,hqS,lt_of_lt_of_le (by linarith) (le_max_right _ _),?_⟩
  intro R hR
  have h1 : R₁ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have h2 : R₂ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hS1 : S+1 ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  refine ⟨hreg R h1,?_⟩
  intro i x hr ht hx
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (by linarith : S < ‖x‖),
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by linarith : ‖x‖ < (7/2)*R),
    (polarCone_open _ (q.patch i).region_open).mem_nhds hx] with z hzS hzT hzc
  by_cases hzR : ‖z‖ ≤ R
  · have hh := hinner R i z hzS.le hzR hzc
    simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hzR]
    exact ⟨hh.1.symm,hh.2.symm⟩
  · by_cases hz3 : ‖z‖ ≤ 3*R
    · have hh := q.local_eq hRp (hq₁.trans_le h1)
        (fun i y hr ht hw => (hreg R h1 i y hr ht hw).1) (le_of_not_ge hzR) hz3 hzc
      simpa only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
        ite_eq_right hzR,ite_eq_left hz3] using hh
    · have hh := houter R h2 i z (lt_of_not_ge hz3) hzT hzc
      simpa only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
        ite_eq_right hzR,ite_eq_right hz3] using And.intro hh.1.symm hh.2.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients
open scoped ContDiff Matrix.Norms.Elementwise
local instance smrbilNorm : NormedAddCommGroup CKSTangentCoefficients.Bil :=
  ContinuousLinearMap.toNormedAddCommGroup (E := CKSTangentCoefficients.V) (F := CKSTangentCoefficients.V →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrbilSpace : NormedSpace ℝ CKSTangentCoefficients.Bil := ContinuousLinearMap.toNormedSpace
local instance smrepNorm : NormedAddCommGroup (E →L[ℝ] Point →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := Point →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrepSpace : NormedSpace ℝ (E →L[ℝ] Point →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smrpeNorm : NormedAddCommGroup (Point →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Point) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrpeSpace : NormedSpace ℝ (Point →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smreeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smreeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma spatialMatrix_contDiffAt {F : E → CKSAngularGeometry.AmbientMat} {x : E} (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (spatialMatrix F) x := by
  have hB := matrixBilinear_contDiff.contDiffAt.comp x hF
  have hf1 : ContDiff ℝ ∞ (fun B : E →L[ℝ] Point →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] Point →L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E Point ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hf2 : ContDiff ℝ ∞ (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf2.contDiffAt.comp _ ((hf1.contDiffAt.comp _ (hB.clm_comp contDiffAt_const)).clm_comp contDiffAt_const)
lemma spatialMatrix_symm {F : E → CKSAngularGeometry.AmbientMat} {x : E} (h : (F x).IsHermitian) :
    ∀ v w, spatialMatrix F x v w = spatialMatrix F x w v := by
  intro v w
  exact matrixBilinear_symm h _ _
lemma spatialMatrix_pos {F : E → CKSAngularGeometry.AmbientMat} {x : E} (h : (F x).PosDef) :
    ∀ v : E, v ≠ 0 → 0 < spatialMatrix F x v v := by
  intro v hv
  apply matrixBilinear_pos h
  exact (EuclideanSpace.equiv (Fin 3) ℝ).injective.ne (by simpa using hv)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise
lemma metricBlock_smoothAt {a : Point → ℝ} {b : Point → CKSAngularGeometry.Point}
    {q : Point → Mat} {x : Point}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hq : ContDiffAt ℝ ∞ q x) :
    ContDiffAt ℝ ∞ (fun y => metricBlock (a y) (b y) (q y)) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · exact ha
    · fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
  · refine Fin.cases ?_ (fun d => ?_) j
    · fin_cases c <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
    · fin_cases c <;> fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
lemma sourceMetric_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceMetric f.base) y :=
  metricBlock_smoothAt (sourceRadialMetric_smoothAt hf.base hy) hf.base.b (sourceGamma_smoothAt hf.base hy)
lemma sourceTensor_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceTensor f) y :=
  metricBlock_smoothAt (sourceRadialK_smoothAt hf) hf.kb (sourceTangentialK_smoothAt hf.base hy)
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_spatial_regular {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v)
    {x : E} (hx : q.radius < ‖x‖) :
    ContDiffAt ℝ ∞ (sourceSpatial A) x ∧ ContDiffAt ℝ ∞ (sourceSpatial B) x ∧
    (∀ v w, sourceSpatial A x v w = sourceSpatial A x w v) ∧
    (∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v) ∧
    ∀ v w, sourceSpatial B x v w = sourceSpatial B x w v := by
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (q.radius_pos.trans hx),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rwa [hyr],hyw⟩
  have hs := q.source_smooth i y hy
  have hgp := polarLift_smooth_positive (q.patch i).patch (sourceMetric (q.patch i).fields.base)
    hy0 hyt (sourceMetric_smoothAt hs hy0.ne') (q.source_positive i y hy)
  have hkt := polarLift_smoothAt (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (sourceTensor_smoothAt hs hy0.ne')
  have hks := polarLift_symmetric (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (metricBlock_hermitian _ _ (q.source_symmetric i y hy))
  rw [hyx] at hgp hkt hks
  have he : ∀ᶠ z in 𝓝 x,
      sourceSpatial A z = polarLift (q.patch i).patch (sourceMetric (q.patch i).fields.base) z ∧
      sourceSpatial B z = polarLift (q.patch i).patch (sourceTensor (q.patch i).fields) z := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx,
      (polarCone_open _ (q.patch i).region_open).mem_nhds hc] with z hz hzc
    obtain ⟨hu,huw,hut,huz⟩ := polarCone_inverse (q.patch i).patch hzc
    have hr := spatial_source_reconstruction (q.patch i) hu hut
      (by rw [huz]; exact hA z hz) (by rw [huz]; exact hB z hz)
    rw [huz] at hr
    exact ⟨hr.2.2.1.symm,hr.2.2.2.symm⟩
  refine ⟨hgp.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
    hkt.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
  · rw [he.self_of_nhds.1]; exact hgp.2.1
  · rw [he.self_of_nhds.1]; exact hgp.2.2
  · rw [he.self_of_nhds.2]; exact hks
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

theorem actual_same_end_smooth_replacement {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀,
        ContDiffOn ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        ContDiffOn ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        (∀ x, S < ‖x‖ →
          (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
            q.replacementMetric (heatDatum M hM) m R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
          ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
            q.replacementTensor (heatDatum M hM) m R x w v) ∧
        (∀ x, ‖x‖ ≤ R →
          q.replacementMetric (heatDatum M hM) m R x = sourceSpatial A x ∧
          q.replacementTensor (heatDatum M hM) m R x = sourceSpatial B x) ∧
        (∀ x, 3*R < ‖x‖ →
          q.replacementMetric (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
          q.replacementTensor (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x) ∧
        ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
          physicalDEC (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementMetric (heatDatum M hM) m R) a b z)
            (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementTensor (heatDatum M hM) m R) a b z)
            (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  obtain ⟨S,R₁,hS,hqS,hS₁,hprep⟩ := q.replacement_localization hM hmass m hcharge hA hB
  obtain ⟨R₂,hR₂,houter⟩ := CKSCartesianOuter.constructed_cartesian_outer_regular
    (heatDatum M hM) (heatDatum_smooth hM) m
  refine ⟨S,max R₁ R₂,hS,hqS,hS₁.trans_le (le_max_left _ _),?_⟩
  intro R hR
  have h1 := (le_max_left R₁ R₂).trans hR
  have h2 := (le_max_right R₁ R₂).trans hR
  have hRp : 0 < R := by linarith
  obtain ⟨hpoint,hlocal⟩ := hprep R h1
  have hrall : ∀ x : E, S < ‖x‖ →
      ContDiffAt ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) x ∧
      ContDiffAt ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) x ∧
      (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
        q.replacementMetric (heatDatum M hM) m R x w v) ∧
      (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
      ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
        q.replacementTensor (heatDatum M hM) m R x w v := by
    intro x hx
    by_cases hi : ‖x‖ < R
    · have hs := q.source_spatial_regular hA hB (hqS.trans hx)
      have he : ∀ᶠ z in 𝓝 x,
          q.replacementMetric (heatDatum M hM) m R z = sourceSpatial A z ∧
          q.replacementTensor (heatDatum M hM) m R z = sourceSpatial B z := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hi] with z hz
        simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hz.le]
        exact ⟨trivial,trivial⟩
      refine ⟨hs.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
        hs.2.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
      · rw [he.self_of_nhds.1]; exact hs.2.2.1
      · rw [he.self_of_nhds.1]; exact hs.2.2.2.1
      · rw [he.self_of_nhds.2]; exact hs.2.2.2.2
    · by_cases ho : 3*R < ‖x‖
      · obtain ⟨hg,hk,hpos,hks⟩ := houter R h2 x ho.le
        have he : ∀ᶠ z in 𝓝 x,
            q.replacementMetric (heatDatum M hM) m R z =
              spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) z ∧
            q.replacementTensor (heatDatum M hM) m R z =
              spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) z := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ho] with z hz
          simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
            ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
          exact ⟨trivial,trivial⟩
        refine ⟨(spatialMatrix_contDiffAt hg).congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
          (spatialMatrix_contDiffAt hk).congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
        · rw [he.self_of_nhds.1]; exact spatialMatrix_symm hpos.isHermitian
        · rw [he.self_of_nhds.1]; exact spatialMatrix_pos hpos
        · rw [he.self_of_nhds.2]; exact spatialMatrix_symm hks
      · have hr : R ≤ ‖x‖ := le_of_not_gt hi
        have ht : ‖x‖ ≤ 3*R := le_of_not_gt ho
        let i := q.localIndex x
        have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
          ⟨norm_pos_iff.mp (hRp.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
        obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
        have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
        have hs := (hpoint i (polarInverse (q.patch i).patch x)
          (by rwa [hyr]) (by rwa [hyr]) hyw).1
        have hg := polarLift_smooth_positive (q.patch i).patch _ hy0 hyt hs.metric_smooth hs.metric_positive
        have hk := polarLift_smoothAt (q.patch i).patch _ hy0 hyt hs.tensor_smooth
        have hks := polarLift_symmetric (q.patch i).patch _ hy0 hyt hs.tensor_symmetric
        rw [hyx] at hg hk hks
        have he := hlocal i x hr ht hc
        refine ⟨hg.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
          hk.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
        · rw [he.self_of_nhds.1]; exact hg.2.1
        · rw [he.self_of_nhds.1]; exact hg.2.2
        · rw [he.self_of_nhds.2]; exact hks
  refine ⟨fun x hx => (hrall x hx).1.contDiffWithinAt,
    fun x hx => (hrall x hx).2.1.contDiffWithinAt,fun x hx => (hrall x hx).2.2,?_,?_,?_⟩
  · intro x hx
    simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hx]
    exact ⟨trivial,trivial⟩
  · intro x hx
    simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
      ite_eq_right (by linarith : ¬ ‖x‖ ≤ R),ite_eq_right (not_le.mpr hx)]
    exact ⟨trivial,trivial⟩
  · intro i y hr ht hw
    have hy0 : 0 < y 0 := hRp.trans_le hr
    have hyt := (q.patch i).region_target hw
    have hn := polarParam_norm (q.patch i).patch hy0.le
    have he := hlocal i (polarParam (q.patch i).patch y) (by rwa [hn]) (by rwa [hn])
      (polarCone_param (q.patch i).patch hw hyt hy0)
    have hparam := (polarParam_contDiffAt (q.patch i).patch hyt).continuousAt
    have hcomponents : ∀ᶠ z in 𝓝 y,
        (fun a b => polarTensorComponents (q.patch i).patch
          (q.replacementMetric (heatDatum M hM) m R) a b z) =
          physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) z ∧
        (fun a b => polarTensorComponents (q.patch i).patch
          (q.replacementTensor (heatDatum M hM) m R) a b z) =
          physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields) z := by
      filter_upwards [hparam.tendsto.eventually he,
        (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hy0,
        angularProjection.continuous.continuousAt.preimage_mem_nhds
          ((q.patch i).patch.chart.open_target.mem_nhds hyt)] with z hz hz0 hzt
      constructor
      · ext a b
        change q.replacementMetric (heatDatum M hM) m R (polarParam (q.patch i).patch z) _ _ = _
        rw [hz.1]
        exact polarLift_components (q.patch i).patch _ hz0 hzt a b
      · ext a b
        change q.replacementTensor (heatDatum M hM) m R (polarParam (q.patch i).patch z) _ _ = _
        rw [hz.2]
        exact polarLift_components (q.patch i).patch _ hz0 hzt a b
    exact (physicalDEC_congr (hcomponents.mono (fun z hz => hz.1))
      (hcomponents.mono (fun z hz => hz.2)) (Eventually.of_forall (fun _ _ => rfl))).mpr
        (hpoint i y hr ht hw).2
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma foliationMetric_lapse_ne_zero {U : ℝ} {γ : Mat} {s : Point}
    (hp : (foliationMetric U γ s).PosDef) : U ≠ 0 := by
  intro h0
  let v : PhysicalPoint := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by intro h; have hh := congrFun h 0; norm_num [v] at hh
  have h := hp.dotProduct_mulVec_pos hv
  rw [foliationMetric_quadratic U (metricBlock_leaf_posDef hp).isHermitian s v,h0] at h
  have hz : (fun a : Fin 2 => v a.succ+s a*v 0) = 0 := by
    ext a; fin_cases a <;> simp [v]
  rw [hz] at h
  simp at h
lemma foliation_smoothOrthonormalAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    SmoothOrthonormalAt (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  exact ⟨foliationMetric_contDiffAt hU hγ hs h0,
    adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1⟩
lemma radialMassLapse_denominators {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint} (hu : radialMassLapse γ s t F x ≠ 0) :
    radialExpansion γ s x ≠ 0 ∧ radialMassRadical t F x ≠ 0 := by
  change Real.sqrt (radialMassRadical t F x) / radialExpansion γ s x ≠ 0 at hu
  constructor
  · exact (div_ne_zero_iff.mp hu).2
  · intro h
    apply (div_ne_zero_iff.mp hu).1
    rw [h,Real.sqrt_zero]
lemma physical_collar_frame_lapse {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hp : (physicalCollarMetric R f x).PosDef) : physicalCollarU R f x ≠ 0 := by
  exact foliationMetric_lapse_ne_zero (U := physicalCollarU R f x)
    (γ := physicalCollarGamma R f x) (s := physicalCollarShift R f x) hp
lemma physical_collar_frame_leaf {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hp : (physicalCollarMetric R f x).PosDef) : (physicalCollarGamma R f x).PosDef := by
  have h := hp.submatrix (Fin.succ_injective 2)
  simpa only [physicalCollarMetric,foliationMetric,metricBlock_submatrix] using h
lemma physical_collar_smoothOrthonormalAt {R : ℝ} (hR : 0 < R) {f : LogCollarData}
    {x : PhysicalPoint} (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hσ : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.sigma z).IsHermitian)
    (he : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.metricError z).IsHermitian)
    (hp : (physicalCollarMetric R f x).PosDef) :
    SmoothOrthonormalAt (physicalCollarMetric R f) (physicalCollarFrame R f) x := by
  have hU0 := physical_collar_frame_lapse hp
  have hγ := physical_collar_frame_leaf hp
  obtain ⟨hd,hu⟩ := radialMassLapse_denominators hU0
  have hUs := physicalCollarU_smoothAt hR hr hf hγ hd hu
  have hγs := physicalCollarGamma_smoothAt R hr hf
  have hss := physicalCollarShift_smoothAt R hr hf
  have hge := physicalCollarGamma_eventually_posDef hr hf hσ he hγ
  exact foliation_smoothOrthonormalAt (U := physicalCollarU R f)
    (γ := physicalCollarGamma R f) (s := physicalCollarShift R f) hUs hγs hss hU0 hge
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_orthonormal {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    SmoothOrthonormalAt (sourceMetric (q.patch i).fields.base)
      (sourceFrame (q.patch i).fields.base) y := by
  have hr : y 0 ≠ 0 := (q.radius_pos.trans hy.1).ne'
  have hf := q.source_smooth i y hy
  have hp := q.positive_eventually i hy
  have hγ : ∀ᶠ z in 𝓝 y, (sourceGamma (q.patch i).fields.base z).PosDef :=
    hp.mono fun _ h => metricBlock_leaf_posDef h
  have h := foliation_smoothOrthonormalAt
    (sourceLapse_smoothAt hf.base hr hp.self_of_nhds) (sourceGamma_smoothAt hf.base hr)
    (sourceShift_smoothAt hf.base hr hp.self_of_nhds) (sourceLapse_pos hp.self_of_nhds).ne' hγ
  exact h.congr_metric (hp.mono (fun z hz => (source_metric_foliation hz).symm))
lemma SourceCollarAtlas.collar_data_smooth {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    (sourceCollarData (q.patch i).fields.logFields).SmoothAt (radiusLogPoint y) := by
  have hr : 0 < y 0 := q.radius_pos.trans hy.1
  have hf := q.source_smooth i y hy
  have hp := q.positive_eventually i hy
  have hs : determinant ((q.patch i).fields.base.logFields.sigma (radiusLogPoint y)) ≠ 0 := by
    change determinant (angularRoundMetric (q.patch i).patch.param (angularProjection (radiusLogPoint y))) ≠ 0
    rw [angularProjection_radiusLogPoint,determinant_eq]
    exact ((q.patch i).patch.roundMetric_posDef ((q.patch i).region_target hy.2)).det_pos.ne'
  apply sourceCollarData_smoothAt _ _ hs
  · rwa [logRadiusChart_radiusLogPoint hr]
  · rwa [logRadiusChart_radiusLogPoint hr]
lemma SourceCollarAtlas.collar_symmetries {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).sigma z).IsHermitian) ∧
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).metricError z).IsHermitian) ∧
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).tauDivR2 z).IsHermitian) := by
  have hr : 0 < y 0 := q.radius_pos.trans hy.1
  apply sourceCollar_symmetries
  · rw [logRadiusChart_radiusLogPoint hr]; exact q.positive_eventually i hy
  · apply (q.patch i).sigma_eventually
    simpa only [angularProjection_radiusLogPoint] using hy.2
  · rw [logRadiusChart_radiusLogPoint hr]; exact q.symmetric_eventually i hy
lemma SourceCollarAtlas.collar_orthonormal_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {R : ℝ} (hR : 0 < R) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region)
    (hp : (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) y).PosDef) :
    ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt
      (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
      (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) z := by
  have hr : y 0 ≠ 0 := (q.radius_pos.trans hy.1).ne'
  have hf := q.collar_data_smooth i hy
  obtain ⟨hσ,he,_⟩ := q.collar_symmetries i hy
  have hU0 : physicalCollarU R (sourceCollarData (q.patch i).fields.logFields) y ≠ 0 :=
    physical_collar_frame_lapse hp
  have hγ := physicalCollarGamma_eventually_posDef hr hf hσ he (physical_collar_frame_leaf hp)
  obtain ⟨hd,hu⟩ := radialMassLapse_denominators hU0
  have hUs := physicalCollarU_smoothAt hR hr hf (physical_collar_frame_leaf hp) hd hu
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy,
    hγ,hUs.continuousAt.eventually_ne hU0] with z hz hgz huz
  obtain ⟨hσz,hez,_⟩ := q.collar_symmetries i hz
  exact physical_collar_smoothOrthonormalAt hR (q.radius_pos.trans hz.1).ne'
    (q.collar_data_smooth i hz) hσz hez (foliationMetric_posDef huz hgz _)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
abbrev cartesianPolar (P : SmoothAngularPatch) (y : Point) : Point :=
  CKSCartesianOuter.toPoint (polarParam P y)
lemma cartesianPolar_smoothAt (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    ContDiffAt ℝ ∞ (cartesianPolar P) y :=
  CKSCartesianOuter.toPoint.contDiff.contDiffAt.comp y (polarParam_contDiffAt P hy)
lemma cartesianPolar_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (cartesianPolar P) y =
      CKSCartesianOuter.toPoint.toContinuousLinearMap.comp (fderiv ℝ (polarParam P) y) := by
  change fderiv ℝ (CKSCartesianOuter.toPoint ∘ polarParam P) y = _
  rw [fderiv_comp y CKSCartesianOuter.toPoint.differentiableAt
    ((polarParam_contDiffAt P hy).differentiableAt (by simp)),ContinuousLinearEquiv.fderiv]
noncomputable def polarDerivative (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (cartesianPolar P) y)
    (LinearMap.ker_eq_bot.mpr (by
      rw [cartesianPolar_fderiv P hy]
      exact CKSCartesianOuter.toPoint.injective.comp (polarParam_fderiv_injective P hr hy)))
    (LinearMap.range_eq_top.mpr (by
      rw [cartesianPolar_fderiv P hy]
      exact CKSCartesianOuter.toPoint.surjective.comp (polarParam_fderiv_surjective P hr hy)))
lemma polarDerivative_hasFDerivAt (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    HasFDerivAt (cartesianPolar P) (polarDerivative P hr hy).toContinuousLinearMap y :=
  (cartesianPolar_smoothAt P hy).differentiableAt (by simp) |>.hasFDerivAt
noncomputable def polarCartesianChart (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    OpenPartialHomeomorph Point Point :=
  (cartesianPolar_smoothAt P hy).toOpenPartialHomeomorph (cartesianPolar P)
    (polarDerivative_hasFDerivAt P hr hy) (by simp)
@[simp] lemma polarCartesianChart_coe (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (polarCartesianChart P hr hy : Point → Point) = cartesianPolar P := rfl
lemma polarCartesianChart_mem (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    y ∈ (polarCartesianChart P hr hy).source :=
  (cartesianPolar_smoothAt P hy).mem_toOpenPartialHomeomorph_source
    (polarDerivative_hasFDerivAt P hr hy) (by simp)
lemma polarCartesianChart_smooth (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (polarCartesianChart P hr hy) z) ∧
    ∀ᶠ z in 𝓝 (cartesianPolar P y), ContDiffAt ℝ ∞ (polarCartesianChart P hr hy).symm z := by
  let e := polarCartesianChart P hr hy
  have hex : y ∈ e.source := polarCartesianChart_mem P hr hy
  have hnear : ∀ᶠ z in 𝓝 y, 0 < z 0 ∧ angularProjection z ∈ P.chart.target :=
    Filter.inter_mem ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr)
      (angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy))
  refine ⟨hnear.mono (fun z hz => cartesianPolar_smoothAt P hz.2),?_⟩
  have hn : ∀ᶠ z in 𝓝 (e y), 0 < (e.symm z) 0 ∧ angularProjection (e.symm z) ∈ P.chart.target :=
    (e.symm.continuousAt (e.map_source hex)).eventually (e.left_inv hex ▸ hnear)
  filter_upwards [e.open_target.mem_nhds (e.map_source hex),hn] with z hz hreg
  exact e.contDiffAt_symm hz (polarDerivative_hasFDerivAt P hreg.1 hreg.2)
    (cartesianPolar_smoothAt P hreg.2)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators
lemma spatialCoefficients_pair (A : SpatialTensor) (y v w : PhysicalPoint) :
    metricPair (spatialCoefficients A y) v w =
      A (CKSCartesianOuter.toPoint.symm y) (CKSCartesianOuter.toPoint.symm v)
        (CKSCartesianOuter.toPoint.symm w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,spatialCoefficients,metricPair]
  simp only [Fin.sum_univ_three]
  ring
lemma spatialCoefficients_pullback (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.chart.target) :
    coordinatePullback (cartesianPolar P) (spatialCoefficients A) y =
      fun i j => polarTensorComponents P A i j y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,cartesianPolar_fderiv P hy]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,cartesianPolar,polarTensorComponents]
  rfl
lemma spatialCoefficients_spatialMatrix (F : E → AmbientMat) :
    spatialCoefficients (spatialMatrix F) = fun y => F (CKSCartesianOuter.toPoint.symm y) := by
  funext y i j
  unfold spatialCoefficients
  rw [spatialMatrix_apply]
  simp [CKSSphericalChart.pair,CKSMixedGeometry.basis,ite_mul,mul_ite]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma spatialDEC_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) : spatialDEC A B x ↔ spatialDEC C D x := by
  have he (P Q : SpatialTensor) (h : P =ᶠ[𝓝 x] Q) :
      spatialCoefficients P =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)] spatialCoefficients Q := by
    have hh := CKSCartesianOuter.toPoint.symm.continuous.continuousAt.eventually
      (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ h)
    filter_upwards [hh] with y hy
    ext i j
    change P (CKSCartesianOuter.toPoint.symm y) _ _ = Q (CKSCartesianOuter.toPoint.symm y) _ _
    rw [hy]
  unfold spatialDEC
  rw [physicalMetricJet_congr (he A C hA),physicalTensorJet_congr (he B D hB)]
lemma spatialDEC_of_polar {A B : SpatialTensor} (P : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hg : (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] G)
    (hk : (fun z => fun i j => polarTensorComponents P B i j z) =ᶠ[𝓝 y] K)
    (hE : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt G E z)
    (hK : ContDiffAt ℝ ∞ K y) (hs : (K y).IsHermitian)
    (hDEC : physicalDEC G K E y) : spatialDEC A B (polarParam P y) := by
  let e := polarCartesianChart P hr hy
  have hsrc : y ∈ e.source := polarCartesianChart_mem P hr hy
  obtain ⟨he,hi⟩ := polarCartesianChart_smooth P hr hy
  have hEq (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =ᶠ[𝓝 y]
      (fun z => fun i j => polarTensorComponents P F i j z) := by
    filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
      (P.chart.open_target.mem_nhds hy)] with z hz
    exact spatialCoefficients_pullback P F hz
  have hG := (hEq A).trans hg
  have hT := (hEq B).trans hk
  have hframe : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt (coordinatePullback e (spatialCoefficients A)) E z := by
    filter_upwards [hE,hG.eventually_nhds] with z hz heq
    exact hz.congr_metric heq
  have hTsm := hK.congr_of_eventuallyEq hT
  have hTs : (coordinatePullback e (spatialCoefficients B) y).IsHermitian := by
    rwa [hT.self_of_nhds]
  have ht := local_coordinate_DEC_pushforward e (spatialCoefficients A) (spatialCoefficients B) E
    hsrc he hi hframe hTsm hTs
  apply ht.mpr
  rw [physicalMetricJet_congr hG,physicalTensorJet_congr hT]
  have h := hE.self_of_nhds
  exact (physical_coordinate_DEC_iff h.metric_smooth hK h.frame_smooth h.positive h.symmetric hs
    h.orthonormal).mp hDEC
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_spatial_DEC {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v)
    {x : E} (hx : q.radius < ‖x‖) : spatialDEC (sourceSpatial A) (sourceSpatial B) x := by
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (q.radius_pos.trans hx),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rwa [hyr],hyw⟩
  have hn : ∀ᶠ z in 𝓝 y, z ∈ angularRadialTail q.radius (q.patch i).region :=
    (angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy
  have he : ∀ᶠ z in 𝓝 y,
      (fun a b => polarTensorComponents (q.patch i).patch (sourceSpatial A) a b z) =
        sourceMetric (q.patch i).fields.base z ∧
      (fun a b => polarTensorComponents (q.patch i).patch (sourceSpatial B) a b z) =
        sourceTensor (q.patch i).fields z := by
    filter_upwards [hn] with z hz
    have hz0 := q.radius_pos.trans hz.1
    have hzr : q.radius < ‖polarParam (q.patch i).patch z‖ := by
      rw [polarParam_norm _ hz0.le]; exact hz.1
    have h := spatial_source_reconstruction (q.patch i) hz0 ((q.patch i).region_target hz.2)
      (hA _ hzr) (hB _ hzr)
    exact ⟨h.1.symm,h.2.1.symm⟩
  have h := spatialDEC_of_polar (q.patch i).patch hy0 hyt
    (sourceMetric (q.patch i).fields.base) (sourceTensor (q.patch i).fields)
    (sourceFrame (q.patch i).fields.base) (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)
    (hn.mono fun z hz => q.source_orthonormal i hz)
    (sourceTensor_smoothAt (q.source_smooth i y hy) hy0.ne')
    (metricBlock_hermitian _ _ (q.source_symmetric i y hy)) (q.source_DEC i y hy)
  rwa [hyx] at h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensorComponents_smoothAt (P : SmoothAngularPatch) {A : SpatialTensor}
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.chart.target)
    (hA : ContDiffAt ℝ ∞ A (polarParam P y)) (i j : CKSMixedGeometry.I) :
    ContDiffAt ℝ ∞ (polarTensorComponents P A i j) y := by
  have hp := polarParam_contDiffAt P hy
  have hd := hp.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  exact ((hA.comp y hp).clm_apply (hd.clm_apply contDiffAt_const)).clm_apply
    (hd.clm_apply contDiffAt_const)
lemma original_source_fields_smooth {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : y 0 ≠ 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hAs : ContDiffAt ℝ ∞ A (polarParam P.patch y))
    (hBs : ContDiffAt ℝ ∞ B (polarParam P.patch y))
    (hmr : ContDiffAt ℝ ∞ P.mr (angularProjection y))
    (hmg : ∀ a b, ContDiffAt ℝ ∞ (P.mg a b) (angularProjection y))
    (hmK : ∀ a b, ContDiffAt ℝ ∞ (P.mK a b) (angularProjection y)) : P.fields.SmoothAt y := by
  have hA := polarTensorComponents_smoothAt P.patch hy hAs
  have hB := polarTensorComponents_smoothAt P.patch hy hBs
  have hl (a : ℕ) (m : Angle → ℝ) (hm : ContDiffAt ℝ ∞ m (angularProjection y)) :
      ContDiffAt ℝ ∞ (ordinaryLeadingComponent a m) y := by
    unfold ordinaryLeadingComponent
    exact (contDiffAt_const.div
      ((ContinuousLinearMap.proj (0:CKSMixedGeometry.I) : CKSMixedGeometry.Point →L[ℝ] ℝ).contDiff.contDiffAt.pow a)
      (pow_ne_zero a hr)).mul (hm.comp y angularProjection.contDiff.contDiffAt)
  refine ⟨⟨?_,?_,?_,hmr,?_,?_,?_,?_⟩,hB 0 0,?_⟩
  · exact P.patch.roundMetric_contDiffAt hy
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hmg i.succ j.succ
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hmK i.succ j.succ
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hA i.succ j.succ).sub (hl 1 _ (hmg _ _))
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (hB i.succ j.succ).sub (hl 1 _ (hmK _ _))
  · exact contDiffAt_pi.mpr fun i => hA 0 i.succ
  · exact (hA 0 0).sub (hl 5 _ hmr)
  · exact contDiffAt_pi.mpr fun i => hB 0 i.succ
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
lemma sourceSpatial_symmetric {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v) :
    ∀ v w, sourceSpatial A x v w = sourceSpatial A x w v := by
  intro v w
  change hyperbolicField x v w + A x v w = hyperbolicField x w v + A x w v
  rw [hA v w,hyperbolicField_apply,hyperbolicField_apply]
  simp only [hyperbolicMetric,real_inner_comm v w]
  ring
lemma polarTensorComponents_pair (P : SmoothAngularPatch) (A : SpatialTensor)
    (y v w : CKSMixedGeometry.Point) :
    metricPair (fun i j => polarTensorComponents P A i j y) v w =
      A (polarParam P y) (fderiv ℝ (polarParam P) y v) (fderiv ℝ (polarParam P) y w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,polarTensorComponents,metricPair]
  simp only [Fin.sum_univ_three]
  ring
lemma polarTensorComponents_posDef (P : SmoothAngularPatch) {A : SpatialTensor}
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < A (polarParam P y) v v) :
    Matrix.PosDef (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (polarTensorComponents_hermitian P A y hA)
  intro v hv
  have hz : fderiv ℝ (polarParam P) y v ≠ 0 := by
    simpa only [map_zero] using (polarParam_fderiv_injective P hr hy).ne hv
  have h := hp _ hz
  rw [← polarTensorComponents_pair P A y v v] at h
  simpa only [metricPair,dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial,
    mul_assoc,mul_left_comm,mul_comm] using h
lemma physicalDEC_of_spatial {A B : SpatialTensor} (P : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hg : (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] G)
    (hk : (fun z => fun i j => polarTensorComponents P B i j z) =ᶠ[𝓝 y] K)
    (hE : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt G E z)
    (hK : ContDiffAt ℝ ∞ K y) (hs : (K y).IsHermitian)
    (hDEC : spatialDEC A B (polarParam P y)) : physicalDEC G K E y := by
  let e := polarCartesianChart P hr hy
  have hsrc : y ∈ e.source := polarCartesianChart_mem P hr hy
  obtain ⟨he,hi⟩ := polarCartesianChart_smooth P hr hy
  have hEq (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =ᶠ[𝓝 y]
      (fun z => fun i j => polarTensorComponents P F i j z) := by
    filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
      (P.chart.open_target.mem_nhds hy)] with z hz
    exact spatialCoefficients_pullback P F hz
  have hG := (hEq A).trans hg
  have hT := (hEq B).trans hk
  have hframe : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt (coordinatePullback e (spatialCoefficients A)) E z := by
    filter_upwards [hE,hG.eventually_nhds] with z hz heq
    exact hz.congr_metric heq
  have hTsm := hK.congr_of_eventuallyEq hT
  have hTs : (coordinatePullback e (spatialCoefficients B) y).IsHermitian := by
    rwa [hT.self_of_nhds]
  have ht := local_coordinate_DEC_pushforward e (spatialCoefficients A) (spatialCoefficients B) E
    hsrc he hi hframe hTsm hTs
  have h := ht.mp hDEC
  rw [physicalMetricJet_congr hG,physicalTensorJet_congr hT] at h
  have hf := hE.self_of_nhds
  exact (physical_coordinate_DEC_iff hf.metric_smooth hK hf.frame_smooth hf.positive hf.symmetric hs
    hf.orthonormal).mpr h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_source_patch_properties {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (hmr : ∀ θ ∈ P.region, ContDiffAt ℝ ∞ P.mr θ)
    (hmg : ∀ a b θ, θ ∈ P.region → ContDiffAt ℝ ∞ (P.mg a b) θ)
    (hmK : ∀ a b θ, θ ∈ P.region → ContDiffAt ℝ ∞ (P.mK a b) θ)
    {y : CKSMixedGeometry.Point} (hy : y ∈ angularRadialTail S P.region) :
    P.fields.SmoothAt y ∧ (sourceMetric P.fields.base y).PosDef ∧
    (sourceTangentialK P.fields.base y).IsHermitian ∧
    physicalDEC (sourceMetric P.fields.base) (sourceTensor P.fields)
      (sourceFrame P.fields.base) y := by
  have radial {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      S < ‖polarParam P.patch z‖ := by
    rw [polarParam_norm P.patch (hS.trans hz.1).le]; exact hz.1
  have hrec := fun {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) =>
    spatial_source_reconstruction P (hS.trans hz.1) (P.region_target hz.2)
      (hA _ (radial hz)) (hB _ (radial hz))
  have hs {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) : P.fields.SmoothAt z :=
    original_source_fields_smooth P (hS.trans hz.1).ne' (P.region_target hz.2)
      (hAs _ (radial hz)) (hBs _ (radial hz)) (hmr _ hz.2)
      (fun a b => hmg a b _ hz.2) (fun a b => hmK a b _ hz.2)
  have hp {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceMetric P.fields.base z).PosDef := by
    rw [(hrec hz).1]
    exact polarTensorComponents_posDef P.patch (hS.trans hz.1) (P.region_target hz.2)
      (sourceSpatial_symmetric (hA _ (radial hz))) (hpos _ (radial hz))
  have hks {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceTensor P.fields z).IsHermitian := by
    rw [(hrec hz).2.1]
    exact polarTensorComponents_hermitian P.patch _ z (sourceSpatial_symmetric (hB _ (radial hz)))
  have hk {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      (sourceTangentialK P.fields.base z).IsHermitian := by
    have h := (hks hz).submatrix (fun i : Fin 2 => i.succ)
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have he {z : CKSMixedGeometry.Point} (hz : z ∈ angularRadialTail S P.region) :
      SmoothOrthonormalAt (sourceMetric P.fields.base) (sourceFrame P.fields.base) z := by
    have hpe : ∀ᶠ w in 𝓝 z, (sourceMetric P.fields.base w).PosDef :=
      Filter.Eventually.mono ((angularRadialTail_open S P.region_open).mem_nhds hz) (fun _ hw => hp hw)
    have hγ : ∀ᶠ w in 𝓝 z, (sourceGamma P.fields.base w).PosDef :=
      hpe.mono fun _ hw => metricBlock_leaf_posDef hw
    have h := foliation_smoothOrthonormalAt
      (sourceLapse_smoothAt (hs hz).base (hS.trans hz.1).ne' (hp hz))
      (sourceGamma_smoothAt (hs hz).base (hS.trans hz.1).ne')
      (sourceShift_smoothAt (hs hz).base (hS.trans hz.1).ne' (hp hz))
      (sourceLapse_pos (hp hz)).ne' hγ
    exact h.congr_metric (hpe.mono (fun w hw => (source_metric_foliation hw).symm))
  refine ⟨hs hy,hp hy,hk hy,?_⟩
  have hn : ∀ᶠ z in 𝓝 y, z ∈ angularRadialTail S P.region :=
    (angularRadialTail_open S P.region_open).mem_nhds hy
  exact physicalDEC_of_spatial P.patch (hS.trans hy.1) (P.region_target hy.2)
    (sourceMetric P.fields.base) (sourceTensor P.fields) (sourceFrame P.fields.base)
    (hn.mono fun z hz => (hrec hz).1.symm) (hn.mono fun z hz => (hrec hz).2.1.symm)
    (hn.mono fun z hz => he hz) (sourceTensor_smoothAt (hs hy) (hS.trans hy.1).ne')
    (hks hy) (hDEC _ (radial hy))
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry
open scoped BigOperators

def matrixLeaf (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Mat :=
  fun i j => G x i.succ j.succ
def matrixMixed (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Point :=
  fun i => G x 0 i.succ
def matrixShift (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Point :=
  fun i => ∑ j, inverse (matrixLeaf G x) i j * matrixMixed G x j
def matrixSchur (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : ℝ :=
  G x 0 0 - ∑ i, ∑ j, inverse (matrixLeaf G x) i j * (matrixMixed G x i * matrixMixed G x j)
def matrixLapse (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : ℝ :=
  1/Real.sqrt (matrixSchur G x)
def matrixFrame (G : PhysicalPoint → AmbientMat) : LocalFrame :=
  fun i x => adaptedFrame (matrixLapse G x) (matrixLeaf G x) (matrixShift G x) i
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry Matrix Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
lemma actual_matrix_block {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) :
    metricBlock (G x 0 0) (matrixMixed G x) (matrixLeaf G x) = G x := by
  have h10 := hermitian_real_symmetry hs 1 0
  have h20 := hermitian_real_symmetry hs 2 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metricBlock,matrixMixed,matrixLeaf,h10,h20]
lemma actual_matrix_leaf_pos {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) : (matrixLeaf G x).PosDef :=
  hp.submatrix (Fin.succ_injective 2)
lemma actual_matrix_schur_pos {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) : 0 < matrixSchur G x := by
  apply metricBlock_schur_positive
  rwa [actual_matrix_block hp.isHermitian]
lemma actual_matrix_foliation {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hp : (G x).PosDef) :
    foliationMetric (matrixLapse G x) (matrixLeaf G x) (matrixShift G x) = G x := by
  have hq : determinant (matrixLeaf G x) ≠ 0 := by
    rw [determinant_eq]; exact (actual_matrix_leaf_pos hp).det_pos.ne'
  have hs := actual_matrix_schur_pos hp
  have hr : 1/(matrixLapse G x)^2 = matrixSchur G x := by
    rw [matrixLapse,div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold foliationMetric
  rw [hr]
  have hv : (fun a => ∑ b, matrixLeaf G x a b * matrixShift G x b) = matrixMixed G x := by
    funext a
    exact inverse_mul_vector (matrixLeaf G x) hq (matrixMixed G x) a
  rw [hv,← actual_matrix_block hp.isHermitian]
  congr 1
  unfold matrixSchur matrixShift
  rw [inverse_quadratic _ hq]
  ring
lemma actual_matrix_frame {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ContDiffAt ℝ ∞ G x) (hp : ∀ᶠ y in 𝓝 x, (G y).PosDef) :
    SmoothOrthonormalAt G (matrixFrame G) x := by
  have hq : ContDiffAt ℝ ∞ (matrixLeaf G) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_pi.mp (contDiffAt_pi.mp hG _) _
  have hb : ContDiffAt ℝ ∞ (matrixMixed G) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mp (contDiffAt_pi.mp hG _) _
  have hz : determinant (matrixLeaf G x) ≠ 0 := by
    rw [determinant_eq]; exact (actual_matrix_leaf_pos hp.self_of_nhds).det_pos.ne'
  have hi := inverse_smoothAt hq hz
  have hshift : ContDiffAt ℝ ∞ (matrixShift G) x :=
    contDiffAt_pi.mpr fun i => ContDiffAt.sum fun j _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hi i) j).mul (contDiffAt_pi.mp hb j)
  have hschur : ContDiffAt ℝ ∞ (matrixSchur G) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hG 0) 0).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (contDiffAt_pi.mp (contDiffAt_pi.mp hi i) j).mul
          ((contDiffAt_pi.mp hb i).mul (contDiffAt_pi.mp hb j)))
  have hpos := actual_matrix_schur_pos hp.self_of_nhds
  have hu : ContDiffAt ℝ ∞ (matrixLapse G) x :=
    contDiffAt_const.div (hschur.sqrt hpos.ne') (Real.sqrt_ne_zero'.mpr hpos)
  have hpU : 0 < matrixLapse G x := one_div_pos.mpr (Real.sqrt_pos.mpr hpos)
  have h := foliation_smoothOrthonormalAt hu hq hshift hpU.ne'
    (hp.mono fun _ h => actual_matrix_leaf_pos h)
  exact h.congr_metric (hp.mono fun _ h => (actual_matrix_foliation h).symm)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
local instance sgpNorm : NormedAddCommGroup SpatialBilinear :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance sgpSpace : NormedSpace ℝ SpatialBilinear := ContinuousLinearMap.toNormedSpace
lemma spatialTensorPullback_smooth {F : E → E} {A : SpatialTensor} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (hA : ContDiffAt ℝ ∞ A (F x)) :
    ContDiffAt ℝ ∞ (spatialTensorPullback F A) x := by
  have hD := hF.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hf : ContDiff ℝ ∞ (fun B : SpatialBilinear => B.flip) := by
    let L : SpatialBilinear →L[ℝ] SpatialBilinear :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf.contDiffAt.comp _ ((hf.contDiffAt.comp _ ((hA.comp x hF).clm_comp hD)).clm_comp hD)
lemma spatialCoefficients_smooth {A : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (spatialCoefficients A) (CKSCartesianOuter.toPoint x) := by
  have h := hA.comp (CKSCartesianOuter.toPoint x) CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  exact (h.clm_apply contDiffAt_const).clm_apply contDiffAt_const
lemma spatialCoefficients_symmetric {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simpa [spatialCoefficients] using (hA (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis i))
    (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis j))).symm
lemma spatialCoefficients_positive {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (spatialCoefficients_symmetric hA)
  intro v hv
  have hz : CKSCartesianOuter.toPoint.symm v ≠ 0 := by
    simpa only [map_zero] using CKSCartesianOuter.toPoint.symm.injective.ne hv
  have h := hp _ hz
  have he := spatialCoefficients_pair A (CKSCartesianOuter.toPoint x) v v
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  rw [← he] at h
  simpa only [metricPair,dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial,
    mul_assoc,mul_left_comm,mul_comm] using h
noncomputable def spatialCoordinateHomeomorph (h : E ≃ₜ E) : PhysicalPoint ≃ₜ PhysicalPoint :=
  CKSCartesianOuter.toPoint.symm.toHomeomorph.trans (h.trans CKSCartesianOuter.toPoint.toHomeomorph)
lemma spatialCoordinateHomeomorph_smooth (h : E ≃ₜ E) {x : E}
    (hF : ContDiffAt ℝ ∞ h x) :
    ContDiffAt ℝ ∞ (spatialCoordinateHomeomorph h) (CKSCartesianOuter.toPoint x) := by
  change ContDiffAt ℝ ∞ (CKSCartesianOuter.toPoint ∘ h ∘ CKSCartesianOuter.toPoint.symm) _
  exact CKSCartesianOuter.toPoint.contDiff.contDiffAt.comp _
    (hF.comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt)
lemma spatialCoordinateHomeomorph_fderiv (h : E ≃ₜ E) {y : PhysicalPoint}
    (hF : DifferentiableAt ℝ h (CKSCartesianOuter.toPoint.symm y)) :
    fderiv ℝ (spatialCoordinateHomeomorph h) y = CKSCartesianOuter.toPoint.toContinuousLinearMap.comp
      ((fderiv ℝ h (CKSCartesianOuter.toPoint.symm y)).comp CKSCartesianOuter.toPoint.symm.toContinuousLinearMap) := by
  change fderiv ℝ (CKSCartesianOuter.toPoint ∘ h ∘ CKSCartesianOuter.toPoint.symm) y = _
  simp only [fderiv_comp y (CKSCartesianOuter.toPoint.differentiableAt) (hF.comp y CKSCartesianOuter.toPoint.symm.differentiableAt),
    fderiv_comp y hF CKSCartesianOuter.toPoint.symm.differentiableAt,ContinuousLinearEquiv.fderiv]
lemma spatialCoefficients_general_pullback (h : E ≃ₜ E) (A : SpatialTensor) {y : PhysicalPoint}
    (hF : DifferentiableAt ℝ h (CKSCartesianOuter.toPoint.symm y)) :
    coordinatePullback (spatialCoordinateHomeomorph h) (spatialCoefficients A) y =
      spatialCoefficients (spatialTensorPullback h A) y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,spatialCoordinateHomeomorph_fderiv h hF]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,spatialCoordinateHomeomorph,Homeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma spatialDEC_pullback (h : E ≃ₜ E) (hF : ContDiff ℝ ∞ h) (hI : ContDiff ℝ ∞ h.symm)
    (G K : SpatialTensor) {U : Set E} (hU : IsOpen U)
    (hGs : ∀ z ∈ U, ContDiffAt ℝ ∞ G z) (hKs : ∀ z ∈ U, ContDiffAt ℝ ∞ K z)
    (hGsym : ∀ z ∈ U, ∀ v w, G z v w = G z w v)
    (hKsym : ∀ z ∈ U, ∀ v w, K z v w = K z w v)
    (hp : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : h x ∈ U) :
    spatialDEC (spatialTensorPullback h G) (spatialTensorPullback h K) x ↔ spatialDEC G K (h x) := by
  let e := (spatialCoordinateHomeomorph h).toOpenPartialHomeomorph
  have he : ContDiff ℝ ∞ e := CKSCartesianOuter.toPoint.contDiff.comp
    (hF.comp CKSCartesianOuter.toPoint.symm.contDiff)
  have hi : ContDiff ℝ ∞ e.symm := CKSCartesianOuter.toPoint.contDiff.comp
    (hI.comp CKSCartesianOuter.toPoint.symm.contDiff)
  have ex : e (CKSCartesianOuter.toPoint x) = CKSCartesianOuter.toPoint (h x) := by
    simp [e,spatialCoordinateHomeomorph]
  have hc : ∀ y : PhysicalPoint, CKSCartesianOuter.toPoint.symm y ∈ U →
      (spatialCoefficients G y).PosDef := by
    intro y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      spatialCoefficients_positive (hGsym _ hy) (hp _ hy)
  have hn : ∀ᶠ y in 𝓝 (CKSCartesianOuter.toPoint (h x)), CKSCartesianOuter.toPoint.symm y ∈ U := by
    exact CKSCartesianOuter.toPoint.symm.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hU.mem_nhds hx)
  have hE : ∀ᶠ y in 𝓝 (e (CKSCartesianOuter.toPoint x)),
      SmoothOrthonormalAt (spatialCoefficients G) (matrixFrame (spatialCoefficients G)) y := by
    rw [ex]
    filter_upwards [hn] with y hy
    apply actual_matrix_frame
    · simpa only [ContinuousLinearEquiv.apply_symm_apply] using spatialCoefficients_smooth (hGs _ hy)
    · filter_upwards [CKSCartesianOuter.toPoint.symm.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds hy)] with z hz
      exact hc z hz
  have hKsm : ContDiffAt ℝ ∞ (spatialCoefficients K) (e (CKSCartesianOuter.toPoint x)) := by
    rw [ex]; exact spatialCoefficients_smooth (hKs _ hx)
  have hKsy : (spatialCoefficients K (e (CKSCartesianOuter.toPoint x))).IsHermitian := by
    rw [ex]; exact spatialCoefficients_symmetric (hKsym _ hx)
  have ht := local_coordinate_DEC_pullback e (spatialCoefficients G) (spatialCoefficients K)
    (matrixFrame (spatialCoefficients G)) (x := CKSCartesianOuter.toPoint x) (by trivial)
    (Eventually.of_forall fun _ => he.contDiffAt) (Eventually.of_forall fun _ => hi.contDiffAt)
    hE hKsm hKsy
  have eqs (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =
      spatialCoefficients (spatialTensorPullback h F) := by
    funext y
    exact spatialCoefficients_general_pullback h F (hF.differentiable (by simp)).differentiableAt
  rw [eqs G,eqs K,ex] at ht
  exact ht
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass
  spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm

attribute [local instance] OAI.CKSLorentz.hsgSpace

theorem spatialBilinear_isScalarTower : IsScalarTower ℝ ℝ SpatialBilinear where
  smul_assoc scalar factor form := by
    ext first second
    change (scalar * factor) * form first second = scalar * (factor * form first second)
    exact mul_assoc scalar factor (form first second)

attribute [local instance] spatialBilinear_isScalarTower

lemma hyperbolicField_smooth : ContDiff ℝ ∞ hyperbolicField := by
  unfold hyperbolicField
  exact contDiff_const.sub ((contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
    (fun x => by positivity)).smul ((innerSL ℝ).contDiff.smulRight (innerSL ℝ).contDiff))
lemma sourceSpatial_smooth {A : SpatialTensor} {x : E} (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (sourceSpatial A) x := hyperbolicField_smooth.contDiffAt.add hA
lemma sourceSpatial_boost {e : ℝ} {p : E} (he : ‖p‖ < e) (A : SpatialTensor) :
    sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) =
      spatialTensorPullback (hyperbolicMap e (mass e p) p) (sourceSpatial A) := by
  funext x; ext v w
  change hyperbolicField x v w + A _ _ _ = hyperbolicField _ _ _ + A _ _ _
  rw [hyperbolicField_apply,hyperbolicField_apply]
  exact congrArg (fun z : ℝ => z + A _ _ _) (hyperbolicMap_isometry he (mass_pos he) (mass_sq he) x v w).symm
lemma smoothHomeomorph_fderiv_injective (h : E ≃ₜ E) (hs : ContDiff ℝ ∞ h)
    (hi : ContDiff ℝ ∞ h.symm) (x : E) : Function.Injective (fderiv ℝ h x) := by
  have hc : (fderiv ℝ h.symm (h x)).comp (fderiv ℝ h x) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x (hi.differentiable (by simp)).differentiableAt
      (hs.differentiable (by simp)).differentiableAt]
    have hh : h.symm ∘ h = id := funext h.symm_apply_apply
    rw [hh,fderiv_id]
  intro v w hv
  have hi' := congrArg (fderiv ℝ h.symm (h x)) hv
  have hv' := congrArg (fun L : E →L[ℝ] E => L v) hc
  have hw' := congrArg (fun L : E →L[ℝ] E => L w) hc
  change _ = v at hv'; change _ = w at hw'
  exact hv'.symm.trans (hi'.trans hw')

theorem hyperbolic_source_geometry {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) {U : Set E} (hU : IsOpen U)
    (hAs : ∀ z ∈ U, ContDiffAt ℝ ∞ A z)
    (hBs : ∀ z ∈ U, ContDiffAt ℝ ∞ B z)
    (hA : ∀ z ∈ U, ∀ v w, A z v w = A z w v)
    (hB : ∀ z ∈ U, ∀ v w, B z v w = B z w v)
    (hp : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < sourceSpatial A z v v)
    (hDEC : ∀ z ∈ U, spatialDEC (sourceSpatial A) (sourceSpatial B) z)
    {x : E} (hx : hyperbolicMap e (mass e p) p x ∈ U) :
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ContDiffAt ℝ ∞ A' x ∧ ContDiffAt ℝ ∞ B' x ∧
    (∀ v w, A' x v w = A' x w v) ∧
    (∀ v w, B' x v w = B' x w v) ∧
    (∀ v : E, v ≠ 0 → 0 < sourceSpatial A' x v v) ∧
    spatialDEC (sourceSpatial A') (sourceSpatial B') x := by
  dsimp only
  let h := hyperbolicHomeomorph e p he
  have hs : ContDiff ℝ ∞ h := hyperbolicMap_smooth e (mass e p) p
  have hi : ContDiff ℝ ∞ h.symm := hyperbolicMap_smooth e (mass e p) (-p)
  refine ⟨spatialTensorPullback_smooth hs.contDiffAt (hAs _ hx),
    spatialTensorPullback_smooth hs.contDiffAt (hBs _ hx),?_,?_,?_,?_⟩
  · intro v w; exact hA _ hx _ _
  · intro v w; exact hB _ hx _ _
  · rw [sourceSpatial_boost he]
    intro v hv
    apply hp _ hx
    have hd := smoothHomeomorph_fderiv_injective h hs hi x
    have hz := hd.ne hv
    simp only [map_zero] at hz
    convert hz using 1
    rfl
  · rw [sourceSpatial_boost he,sourceSpatial_boost he]
    exact (spatialDEC_pullback h hs hi (sourceSpatial A) (sourceSpatial B) hU
      (fun z hz => sourceSpatial_smooth (hAs z hz))
      (fun z hz => sourceSpatial_smooth (hBs z hz))
      (fun z hz => sourceSpatial_symmetric (hA z hz))
      (fun z hz => sourceSpatial_symmetric (hB z hz)) hp hx).mpr (hDEC _ hx)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable def SpatialBoostPatch.collarSourcePatch {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : SpatialBoostPatch e p he A B Q P θ δ R) {W : Set Angle}
    (hW : IsOpen W) (hsub : W ⊆ Metric.ball θ δ) :
    CollarSourcePatch (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
      (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) where
  patch := P
  region := W
  region_open := hW
  region_target := hsub.trans h.genuine.estimates.ball_target
  radius := R
  mr := lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr
  mg := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg
  mK := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK
  metric_CKS := h.metric_CKS.mono (fun _ hy => ⟨hy.1,hsub hy.2⟩)
  tensor_CKS := h.second_CKS.mono (fun _ hy => ⟨hy.1,hsub hy.2⟩)
lemma SpatialBoostPatch.collarSourcePatch_fields {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : SpatialBoostPatch e p he A B Q P θ δ R) {W : Set Angle}
    (hW : IsOpen W) (hsub : W ⊆ Metric.ball θ δ) :
    (h.collarSourcePatch hW hsub).fields = boostSourceFields e p A B Q P := rfl
lemma homeomorph_maps_far_tail (h : E ≃ₜ E) (S R : ℝ) :
    ∃ T : ℝ, 0 < T ∧ R ≤ T ∧ ∀ x : E, T < ‖x‖ → S < ‖h x‖ := by
  have hc := h.isCompact_preimage.mpr (isCompact_closedBall (0:E) S)
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:E)).mp hc.isBounded
  refine ⟨max 1 (max R r),lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    (le_max_left R r).trans (le_max_right _ _),?_⟩
  intro x hx
  by_contra hn
  have hm : h x ∈ Metric.closedBall (0:E) S := by simpa using (not_lt.mp hn)
  have hb : ‖x‖ ≤ r := by simpa using hr hm
  have hrt : r ≤ max 1 (max R r) := (le_max_right R r).trans (le_max_right _ _)
  linarith
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Matrix

lemma trace_conformal_congruence {d : ℝ} (hd : d ≠ 0)
    (σ J A : AngularMatrix) (hσ : IsUnit σ.det) (hJ : IsUnit J.det) :
    angularMetricTrace (d^2 • (J*σ*J.transpose)) (d⁻¹ • (J*A*J.transpose)) =
      d⁻¹^3 * angularMetricTrace σ A := by
  have hJt : IsUnit J.transpose.det := by simpa using hJ
  have hi : (d^2 • (J*σ*J.transpose))⁻¹ =
      (d^2)⁻¹ • (J.transpose⁻¹ * σ⁻¹ * J⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    rw [← Matrix.mul_assoc σ⁻¹, Matrix.nonsing_inv_mul _ hσ,Matrix.one_mul]
    exact Matrix.nonsing_inv_mul _ hJt
  simp only [angularMetricTrace,hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul]
  have ht : (J.transpose⁻¹ * σ⁻¹ * J⁻¹ * (J*A*J.transpose)).trace = (σ⁻¹*A).trace := by
    calc
      _ = (J.transpose⁻¹ * (σ⁻¹ * A) * J.transpose).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
      _ = (J.transpose * J.transpose⁻¹ * (σ⁻¹*A)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hJt,Matrix.one_mul]
  rw [ht]
  simp only [smul_eq_mul,inv_pow]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularGram_congruence (L : Angle →L[ℝ] E) {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a b : Fin 2) :
    (angularJacobian Φ θ *
      Matrix.gram ℝ (fun i : Fin 2 => L (CKSAngularGeometry.basis i)) *
      (angularJacobian Φ θ).transpose) a b =
    inner ℝ (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis a)))
      (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis b))) := by
  rw [angularJacobian_apply hΦ a,angularJacobian_apply hΦ b]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    conj_trivial,Matrix.gram_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  ring

lemma boundaryChart_regular {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    boundaryChart e (mass e p) p P.param Q.extension θ ∈ Q.chart.target ∧
    ContDiffAt ℝ ∞ (boundaryChart e (mass e p) p P.param Q.extension) θ := by
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ Q.domain :=
    Q.source_domain _ hQ
  constructor
  · change Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.chart.target
    rw [show boundaryAmbient e (mass e p) p (P.param θ)=
      (boundary e p he (P.chart.symm θ):E) from rfl,Q.extension_eq _ hQ]
    exact Q.chart.map_source hQ
  · have hB : ContDiffAt ℝ ∞ (fun η => boundaryAmbient e (mass e p) p (P.param η)) θ :=
      (boundaryAmbient_smooth (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').comp
        (f := P.param) (g := boundaryAmbient e (mass e p) p) θ
        (P.param_contDiffAt hθ)
    exact (Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds hb)).comp θ hB

lemma boundary_param_fderiv {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    (fderiv ℝ Q.param (boundaryChart e (mass e p) p P.param Q.extension θ)).comp
        (fderiv ℝ (boundaryChart e (mass e p) p P.param Q.extension) θ) =
      (fderiv ℝ (boundaryAmbient e (mass e p) p) (P.param θ)).comp (fderiv ℝ P.param θ) := by
  have hs : ContinuousAt (fun η => boundary e p he (P.chart.symm η)) θ :=
    (boundary_smooth e p he).continuous.continuousAt.comp (P.chart.symm.continuousAt hθ)
  have hn : ∀ᶠ η in 𝓝 θ, boundary e p he (P.chart.symm η) ∈ Q.chart.source :=
    hs.preimage_mem_nhds (Q.chart.open_source.mem_nhds hQ)
  have hg : (fun η => Q.param (boundaryChart e (mass e p) p P.param Q.extension η)) =ᶠ[𝓝 θ]
      (fun η => boundaryAmbient e (mass e p) p (P.param η)) := by
    filter_upwards [hn] with η hη
    change Q.param (Q.extension (boundary e p he (P.chart.symm η))) =
      (boundary e p he (P.chart.symm η):E)
    rw [Q.extension_eq _ hη]
    exact Q.param_chart hη
  have hreg := boundaryChart_regular he P Q hθ hQ
  have h := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (Q.param ∘ boundaryChart e (mass e p) p P.param Q.extension) θ =
    fderiv ℝ (boundaryAmbient e (mass e p) p ∘ P.param) θ at h
  rw [fderiv_comp θ ((Q.param_contDiffAt hreg.1).differentiableAt (by simp))
      (hreg.2.differentiableAt (by simp)),
    fderiv_comp θ ((boundaryAmbient_smooth
      (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').differentiableAt (by simp))
      ((P.param_contDiffAt hθ).differentiableAt (by simp))] at h
  exact h

lemma boundary_roundMetric_conformal {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    let Φ := boundaryChart e (mass e p) p P.param Q.extension
    angularJacobian Φ θ * angularRoundMetric Q.param (Φ θ) * (angularJacobian Φ θ).transpose =
      (denominator e (mass e p) p (P.param θ))⁻¹ ^ 2 • angularRoundMetric P.param θ := by
  dsimp only
  ext a b
  change (angularJacobian _ θ * Matrix.gram ℝ (fun i : Fin 2 =>
    fderiv ℝ Q.param _ (CKSAngularGeometry.basis i)) * (angularJacobian _ θ).transpose) a b = _
  rw [angularGram_congruence _ ((boundaryChart_regular he P Q hθ hQ).2.differentiableAt (by simp))]
  have hd := boundary_param_fderiv he P Q hθ hQ
  have ha := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis a)) hd
  have hb := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [ha,hb]
  exact boundary_conformal he (mass_pos he) (mass_sq he) (P.chart.symm θ) _ _
    (P.param_tangent hθ _) (P.param_tangent hθ _)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentz_leading_trace {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mg : I → I → Angle → ℝ) :
    angularMetricTrace (angularRoundMetric P.param θ)
      (fun a b => lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^ 3 *
      angularMetricTrace (angularRoundMetric Q.param (boundaryChart e (mass e p) p P.param Q.extension θ))
        (fun a b => mg a.succ b.succ (boundaryChart e (mass e p) p P.param Q.extension θ)) := by
  let Φ := boundaryChart e (mass e p) p P.param Q.extension
  let J := angularJacobian Φ θ
  let d := denominator e (mass e p) p (P.param θ)
  let σ := angularRoundMetric Q.param (Φ θ)
  let A : AngularMatrix := fun a b => mg a.succ b.succ (Φ θ)
  have hd : d ≠ 0 := (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne'
  have hreg := boundaryChart_regular he P Q hθ hQ
  have hσ : IsUnit σ.det := isUnit_iff_ne_zero.mpr (Q.roundMetric_posDef hreg.1).det_pos.ne'
  have hconf : J*σ*J.transpose = d⁻¹^2 • angularRoundMetric P.param θ :=
    boundary_roundMetric_conformal he P Q hθ hQ
  have hp : (J*σ*J.transpose).PosDef := by
    rw [hconf]
    exact (P.roundMetric_posDef hθ).smul (sq_pos_of_ne_zero (inv_ne_zero hd))
  have hJ : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdet := hp.det_pos.ne'
    simp only [Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero,ne_eq,not_true_eq_false] at hdet
  have hback : angularRoundMetric P.param θ=d^2 • (J*σ*J.transpose) := by
    rw [hconf,smul_smul,inv_pow,mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
  have hψ : ContDiffAt ℝ ∞ Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) :=
    Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds (Q.source_domain _ hQ))
  have hA : (fun a b : Fin 2 =>
      lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
      d⁻¹ • (J*A*J.transpose) := by
    ext a b
    change lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ =
      d⁻¹ * ∑ i : Fin 2, (∑ j : Fin 2, J a j * A j i) * J b i
    rw [lorentzAngularLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mg
      (Eventually.of_forall P.param_sphere) (P.param_contDiffAt hθ) hψ a b]
    simp only [angularCoordinatePullback,J,A,d,Φ,angularJacobian,Fin.sum_univ_two]
    ring
  rw [hback,hA]
  exact trace_conformal_congruence hd σ J A hσ hJ

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
lemma angularMetricTrace_add (σ A B : AngularMatrix) :
    angularMetricTrace σ (A+B)=angularMetricTrace σ A+angularMetricTrace σ B := by
  simp only [angularMetricTrace,Matrix.mul_add,Matrix.trace_add]
lemma angularMetricTrace_smul (σ A : AngularMatrix) (c : ℝ) :
    angularMetricTrace σ (c • A)=c*angularMetricTrace σ A := by
  simp only [angularMetricTrace,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
lemma cksChartMassAspect_split (φ : Angle → E) (mr : Angle → ℝ)
    (mg mK : I → I → Angle → ℝ) (θ : Angle) :
    cksChartMassAspect φ mr mg mK θ =
      angularMetricTrace (angularRoundMetric φ θ) (fun a b => mg a.succ b.succ θ) +
      2*angularMetricTrace (angularRoundMetric φ θ) (fun a b => mK a.succ b.succ θ) + 2*mr θ := by
  let σ := angularRoundMetric φ θ
  let A : AngularMatrix := fun a b => mg a.succ b.succ θ
  let B : AngularMatrix := fun a b => mK a.succ b.succ θ
  change angularMetricTrace σ (A + (2:ℝ) • B) + 2*mr θ =
    angularMetricTrace σ A + 2*angularMetricTrace σ B + 2*mr θ
  rw [angularMetricTrace_add,angularMetricTrace_smul]

theorem lorentz_cks_massAspect {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) :
    cksChartMassAspect P.param (lorentzRadialLeading e (mass e p) p P.param Q.extension mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mK) θ =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.param mr mg mK
        (boundaryChart e (mass e p) p P.param Q.extension θ) := by
  rw [cksChartMassAspect_split,cksChartMassAspect_split,
    lorentz_leading_trace he P Q hθ hQ mg,lorentz_leading_trace he P Q hθ hQ mK,
    lorentzRadialLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mr
      (P.param_sphere θ)]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
lemma genuine_patch_massAspect {M : Sphere → ℝ} {e : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ₀ : Angle} {δ R : ℝ}
    (h : GenuineBoostPatch e p he Q P θ₀ δ R) (hrep : Q.RepresentsMassAspect M)
    {θ : Angle} (hθ : θ ∈ Metric.ball θ₀ δ) :
    cksChartMassAspect P.param
      (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK) θ =
      aspectPullback e p he M (P.chart.symm θ) := by
  have hb := h.boundary_image θ hθ
  rw [lorentz_cks_massAspect he P Q.patch (h.estimates.ball_target hθ) hb.1]
  change (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.patch.param Q.mr Q.mg Q.mK
        (Q.patch.extension (boundary e p he (P.chart.symm θ))) = _
  rw [Q.patch.extension_eq _ hb.1,hrep _ hb]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem source_atlas_from_original {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (_hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    let M' := aspectPullback e p ht M
    ∃ (ι : Type) (q : SourceCollarAtlas A' B' ι) (hM' : SmoothSphere M'),
      Nonempty ι ∧ q.HasMassAspect M' ∧ bondiCharge M' = (mass e p,0) ∧
      SmoothSphere (heatDatum M' hM') ∧ Balanced (heatDatum M' hM') (mass e p) ∧
      ∀ x : E, q.radius < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖ := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
  obtain ⟨s,P,δ,R,K,C,hR,hK,hKpos,hC,hpatch,hbounds,hcover⟩ :=
    exists_uniform_boost_collar_atlas ht A B old hold hreal
  obtain ⟨T,hT,hRT,hfar⟩ := homeomorph_maps_far_tail (hyperbolicHomeomorph e p ht) S R
  have geom (x : E) (hx : T < ‖x‖) := hyperbolic_source_geometry ht A B
    (U := {z | S < ‖z‖}) (isOpen_lt continuous_const continuous_norm)
    hAs hBs hA hB hpos hDEC (hfar x hx)
  let ι := {n : Sphere // n ∈ s}
  have hd (i : ι) : 0 < δ i := by
    have hh := (hpatch i i.2).genuine.estimates.ball_pos
    linarith
  have hsub (i : ι) : Metric.ball ((P i).chart i) (δ i) ⊆
      Metric.ball ((P i).chart i) (2*δ i) := Metric.ball_subset_ball (by linarith [hd i])
  let Q : ι → CollarSourcePatch A' B' := fun i =>
    (hpatch i i.2).collarSourcePatch Metric.isOpen_ball (hsub i)
  have hg (i : ι) (y : CKSMixedGeometry.Point)
      (hy : y ∈ angularRadialTail T (Q i).region) :=
    original_source_patch_properties (Q i) hT
      (fun x hx => (geom x hx).1) (fun x hx => (geom x hx).2.1)
      (fun x hx => (geom x hx).2.2.1) (fun x hx => (geom x hx).2.2.2.1)
      (fun x hx => (geom x hx).2.2.2.2.1) (fun x hx => (geom x hx).2.2.2.2.2)
      (fun θ hθ => ((hpatch i i.2).genuine.estimates.radial_smooth θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ)))
      (fun a b θ hθ => ((hpatch i i.2).genuine.estimates.angular_smooth a b θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ)))
      (fun a b θ hθ => ((hpatch i i.2).genuine.estimates.second_smooth a b θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ))) hy
  let q : SourceCollarAtlas A' B' ι := {
    patch := Q
    radius := T
    radius_pos := hT
    jetSet := K
    jetSet_compact := hK
    jetSet_positive := hKpos
    bound := C
    bound_nonneg := hC
    bounds := by
      intro i θ hθ ρ
      have hb := hbounds i i.2 θ (Metric.ball_subset_closedBall hθ) ρ
      refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,?_⟩
      intro hr
      exact hb.2.2.2.2.2 (hRT.trans_lt hr)
    source_smooth := fun i y hy => (hg i y hy).1
    source_positive := fun i y hy => (hg i y hy).2.1
    source_symmetric := fun i y hy => (hg i y hy).2.2.1
    source_DEC := fun i y hy => (hg i y hy).2.2.2
    covers := by
      intro n
      obtain ⟨i,hi,hn⟩ := hcover n
      exact ⟨⟨i,hi⟩,hn⟩ }
  obtain ⟨hM',hcharge,hsmooth,hbalanced⟩ := balanced_charge_and_heat hM ht
  refine ⟨ι,q,hM',?_,?_,hcharge,hsmooth,hbalanced,hfar⟩
  · obtain ⟨i,_⟩ := q.covers (spatialDirection 0)
    exact ⟨i⟩
  · intro i θ hθ
    exact genuine_patch_massAspect (hpatch i i.2).genuine (hrep _) (hsub i hθ)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology
lemma polar_components_of_lift_eq (P : SmoothAngularPatch) (A : SpatialTensor)
    (F : CKSMixedGeometry.Point → AmbientMat) {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (he : A =ᶠ[𝓝 (polarParam P y)] polarLift P F) :
    (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] F := by
  filter_upwards [(polarParam_contDiffAt P hy).continuousAt.eventually he,
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr,
    angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy)]
    with z hz hz0 hzt
  ext i j
  change A (polarParam P z) _ _ = _
  rw [hz]
  exact polarLift_components P F hz0 hzt i j
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

theorem actual_same_end_DEC {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀, ∀ x : E, S < ‖x‖ →
        spatialDEC (q.replacementMetric (heatDatum M hM) m R)
          (q.replacementTensor (heatDatum M hM) m R) x := by
  obtain ⟨S,R₁,hS,hqS,hS₁,hprep⟩ := q.replacement_localization hM hmass m hcharge hA hB
  obtain ⟨R₂,hR₂,houter⟩ := CKSCartesianOuter.constructed_cartesian_outer_DEC
    (heatDatum M hM) (heatDatum_smooth hM) m
  refine ⟨S,max R₁ R₂,hS,hqS,hS₁.trans_le (le_max_left _ _),?_⟩
  intro R hR x hx
  have h1 := (le_max_left R₁ R₂).trans hR
  have h2 := (le_max_right R₁ R₂).trans hR
  have hRp : 0 < R := by linarith
  obtain ⟨hpoint,hlocal⟩ := hprep R h1
  by_cases hi : ‖x‖ < R
  · have he : ∀ᶠ z in 𝓝 x,
        q.replacementMetric (heatDatum M hM) m R z = sourceSpatial A z ∧
        q.replacementTensor (heatDatum M hM) m R z = sourceSpatial B z := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hi] with z hz
      simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hz.le]
      exact ⟨trivial,trivial⟩
    exact (spatialDEC_congr (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)).mpr
      (q.source_spatial_DEC hA hB (hqS.trans hx))
  · by_cases ho : 3*R < ‖x‖
    · have he : ∀ᶠ z in 𝓝 x,
          q.replacementMetric (heatDatum M hM) m R z =
            spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) z ∧
          q.replacementTensor (heatDatum M hM) m R z =
            spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) z := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ho] with z hz
        simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
          ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
        exact ⟨trivial,trivial⟩
      apply (spatialDEC_congr (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)).mpr
      unfold spatialDEC
      rw [spatialCoefficients_spatialMatrix,spatialCoefficients_spatialMatrix]
      exact houter R h2 x ho.le
    · have hr : R ≤ ‖x‖ := le_of_not_gt hi
      have ht : ‖x‖ ≤ 3*R := le_of_not_gt ho
      let i := q.localIndex x
      have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
        ⟨norm_pos_iff.mp (hRp.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
      obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
      let y := polarInverse (q.patch i).patch x
      have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
      have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rw [hyr]; exact hqS.trans hx,hyw⟩
      have hpr := hpoint i y (by rwa [hyr]) (by rwa [hyr]) hyw
      have hel := hlocal i x hr ht hc
      have hg := polar_components_of_lift_eq (q.patch i).patch
        (q.replacementMetric (heatDatum M hM) m R)
        (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields)) hy0 hyt
        (by rw [hyx]; exact hel.mono (fun _ h => h.1))
      have hk := polar_components_of_lift_eq (q.patch i).patch
        (q.replacementTensor (heatDatum M hM) m R)
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) hy0 hyt
        (by rw [hyx]; exact hel.mono (fun _ h => h.2))
      have h := spatialDEC_of_polar (q.patch i).patch hy0 hyt
        (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) hg hk
        (q.collar_orthonormal_eventually i hRp hy hpr.1.metric_positive)
        hpr.1.tensor_smooth hpr.1.tensor_symmetric hpr.2
      rwa [hyx] at h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics MeasureTheory

attribute [local instance] sixteen_atLeastTwo

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff
lemma spatialCartesian_spatialMatrix (F : E → AmbientMat) :
    spatialCartesian (spatialMatrix F) = F := by
  funext x
  simp only [spatialCartesian,spatialCoefficients_spatialMatrix,
    ContinuousLinearEquiv.symm_apply_apply]
lemma spatialCartesian_congr_at {A B : SpatialTensor} {x : E} (h : A x = B x) :
    spatialCartesian A x = spatialCartesian B x := by
  unfold spatialCartesian spatialCoefficients
  simp only [ContinuousLinearEquiv.symm_apply_apply,h]
  rfl
lemma SourceCollarAtlas.replacement_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    spatialCartesian (q.replacementMetric f₀ m R) x = CKSADM.metric (cartB f₀ m R) x ∧
    q.replacementTensor f₀ m R x = 0 := by
  have hr : ¬ ‖x‖ ≤ R := by nlinarith
  have ht : ¬ ‖x‖ ≤ 3*R := by nlinarith
  have hg : q.replacementMetric f₀ m R x = spatialMatrix (CKSCartesianOuter.metric f₀ m R) x := by
    simp [SourceCollarAtlas.replacementMetric,hr,ht]
  have hk : q.replacementTensor f₀ m R x = spatialMatrix (CKSCartesianOuter.tensor f₀ m R) x := by
    simp [SourceCollarAtlas.replacementTensor,hr,ht]
  refine ⟨?_,?_⟩
  · rw [spatialCartesian_congr_at hg,spatialCartesian_spatialMatrix]
    exact CKSCartesianOuter.metric_tail f₀ m (by linarith) hx.le
  · rw [hk]
    ext v w
    rw [spatialMatrix_apply,CKSCartesianOuter.tensor_tail f₀ m hR hx]
    simp [CKSSphericalChart.pair]
lemma SourceCollarAtlas.replacement_surfaceEnergy_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R r : ℝ} (hR : 12 ≤ R)
    (hr : 2*R^2 < r) :
    spatialADMEnergy (q.replacementMetric f₀ m R) r = surfaceEnergy f₀ m R r := by
  have hrp : 0 < r := lt_of_le_of_lt (by positivity : 0 ≤ 2*R^2) hr
  unfold spatialADMEnergy surfaceEnergy energyIntegrand
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro n
  have hn : 2*R^2 < ‖r • (n:E)‖ := by rwa [norm_radius_sphere hrp]
  have he : (fun y => spatialCartesian (q.replacementMetric f₀ m R) y) =ᶠ[𝓝 (r • (n:E))]
      CKSADM.metric (cartB f₀ m R) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hn] with y hy
    exact (q.replacement_tail f₀ m hR hy).1
  have hd (i j a : Fin 3) : pd a (fun y => spatialCartesian (q.replacementMetric f₀ m R) y i j) (r • (n:E)) =
      pd a (fun y => CKSADM.metric (cartB f₀ m R) y i j) (r • (n:E)) := by
    unfold pd
    have hc : (fun y => spatialCartesian (q.replacementMetric f₀ m R) y i j) =ᶠ[𝓝 (r • (n:E))]
        (fun y => CKSADM.metric (cartB f₀ m R) y i j) :=
      he.mono (fun y hy => congrArg (fun G : AmbientMat => G i j) hy)
    rw [hc.fderiv_eq]
  simp only [hd]
lemma SourceCollarAtlas.replacement_surfaceMomentum_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R r : ℝ} (hR : 12 ≤ R)
    (hr : 2*R^2 < r) :
    spatialADMMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) r = 0 := by
  have hrp : 0 < r := lt_of_le_of_lt (by positivity : 0 ≤ 2*R^2) hr
  have hk (n : Sphere) : spatialCartesian (q.replacementTensor f₀ m R) (r • (n:E)) = 0 := by
    have h := (q.replacement_tail f₀ m hR (x := r • (n:E)) (by rwa [norm_radius_sphere hrp])).2
    unfold spatialCartesian spatialCoefficients
    simp only [ContinuousLinearEquiv.symm_apply_apply,h]
    rfl
  ext i
  simp only [spatialADMMomentum,hk,Matrix.zero_apply,mul_zero,Finset.sum_const_zero,
    zero_mul,sub_zero,integral_zero,Pi.zero_apply]

theorem actual_same_end_AF_ADM {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    (m : ℝ) {R : ℝ} (hR : 12 ≤ R) :
    (∀ x : E, 2*R^2 < ‖x‖ → q.replacementTensor f₀ m R x = 0) ∧
    (∀ i j : Fin 3, Symbol 1 (fun x =>
      spatialCartesian (q.replacementMetric f₀ m R) x i j - (if i=j then 1 else 0))) ∧
    Tendsto (spatialADMEnergy (q.replacementMetric f₀ m R)) atTop (𝓝 (m+paddingCharge R)) ∧
    Tendsto (spatialADMMomentum (q.replacementMetric f₀ m R)
      (q.replacementTensor f₀ m R)) atTop (𝓝 0) ∧
    0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  obtain ⟨hE,hη0,hη1⟩ := constructed_ADM_energy f₀ hf₀ m (R := R) (by linarith)
  refine ⟨fun x hx => (q.replacement_tail f₀ m hR hx).2,?_,?_,?_,hη0,hη1⟩
  · intro i j
    apply (constructed_metric_decay f₀ hf₀ m hR i j).congr
    filter_upwards [eventually_norm_gt (2*R^2)] with x hx
    rw [(q.replacement_tail f₀ m hR hx).1]
  · apply hE.congr'
    filter_upwards [eventually_gt_atTop (2*R^2)] with r hr
    exact (q.replacement_surfaceEnergy_tail f₀ m hR hr).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2*R^2)] with r hr
    exact (q.replacement_surfaceMomentum_tail f₀ m hR hr).symm
end
end CKSLorentz

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def direction (x : E) : Fin 3 → ℝ := fun i => x i / ‖x‖
def tailMetric (F : E → ℝ) (x : E) : Mat :=
  1 + ((1-2*F x/‖x‖)⁻¹-1) • Matrix.vecMulVec (direction x) (direction x)
def density (F : E → ℝ) (x : E) : ℝ := Real.sqrt (tailMetric F x).det
def tailVolume (F : E → ℝ) : Measure E := volume.withDensity (fun x => ENNReal.ofReal (density F x))
def tailRegion (L : ℝ) : Set E := {x | L < ‖x‖}
end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
lemma direction_sq_sum {x : E} (hx : x ≠ 0) : ∑ i, direction x i ^ 2 = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [direction,div_pow,← Finset.sum_div]
  rw [← EuclideanSpace.real_norm_sq_eq x]
  exact div_self (pow_ne_zero _ hn)
lemma det_rank_one (n : Fin 3 → ℝ) (b : ℝ) :
    (1 + b • vecMulVec n n : Mat).det = 1 + b * ∑ i, n i^2 := by
  have he : (b • vecMulVec n n : Mat) =
      replicateCol Unit (b • n) * replicateRow Unit n := by
    ext i j
    simp [Matrix.mul_apply,Matrix.vecMulVec,Matrix.replicateCol,Matrix.replicateRow,mul_assoc]
  rw [he,det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct,Pi.smul_apply,smul_eq_mul]
  simp_rw [show ∀ i, n i * (b * n i) = b * n i^2 by intro i; ring,Finset.mul_sum]
lemma tailMetric_det {x : E} (hx : x ≠ 0) (F : E → ℝ) :
    (tailMetric F x).det = (1-2*F x/‖x‖)⁻¹ := by
  rw [tailMetric,det_rank_one,direction_sq_sum hx]
  ring

theorem tail_density_bound {F : E → ℝ} {M L : ℝ} (_hM : 0 ≤ M) (hL : 0 < L)
    (hML : 4*M ≤ L) (hF : ∀ x ∈ tailRegion L, |F x| ≤ M) :
    ∀ x ∈ tailRegion L, (tailMetric F x).det = (1-2*F x/‖x‖)⁻¹ ∧
      0 ≤ density F x ∧ density F x ≤ Real.sqrt 2 := by
  intro x hx
  have hLx : L < ‖x‖ := hx
  have hr : 0 < ‖x‖ := hL.trans hLx
  have hdet := tailMetric_det (norm_pos_iff.mp hr) F
  refine ⟨hdet,Real.sqrt_nonneg _,?_⟩
  unfold density
  rw [hdet]
  apply Real.sqrt_le_sqrt
  have hfx : F x ≤ M := (le_abs_self _).trans (hF x hx)
  have hhalf : 1/2 ≤ 1-2*F x/‖x‖ := by
    have hdiv : 2*F x/‖x‖ ≤ 1/2 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-2*F x/‖x‖)).mpr
  linarith
end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal
lemma rate_le_japanese {r : ℝ} (hr : 1 ≤ r) :
    1/(r^3*Real.sqrt r) ≤ (2:ℝ)^(7/2:ℝ)*(1+r)^(-(7/2:ℝ)) := by
  have hp : 0 < r := zero_lt_one.trans_le hr
  have he : 1/(r^3*Real.sqrt r) = r^(-(7/2:ℝ)) := by
    rw [Real.rpow_neg hp.le,show (7/2:ℝ) = (3:ℝ)+1/2 by norm_num,
      Real.rpow_add hp,← Real.sqrt_eq_rpow]
    norm_num
  rw [he]
  calc
    _ ≤ ((1+r)/2)^(-(7/2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul,mul_comm]
lemma tailRegion_measurable (L : ℝ) : MeasurableSet (tailRegion L) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

lemma constraint_integrable_dx {κ : E → ℝ} {C L : ℝ}
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hκmeas : Measurable κ)
    (hκ : ∀ x ∈ tailRegion L, |κ x| ≤ C/(‖x‖^3*Real.sqrt ‖x‖)) :
    IntegrableOn κ (tailRegion L) volume := by
  have hh : Integrable (fun x : E => (1+‖x‖)^(-(7/2:ℝ))) volume :=
    integrable_one_add_norm (by norm_num [E,finrank_euclideanSpace])
  apply ((hh.const_mul (C*(2:ℝ)^(7/2:ℝ))).integrableOn).mono' hκmeas.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict (tailRegion_measurable L)] with x hx
  rw [Real.norm_eq_abs]
  calc
    _ ≤ C/(‖x‖^3*Real.sqrt ‖x‖) := hκ x hx
    _ = C * (1/(‖x‖^3*Real.sqrt ‖x‖)) := by ring
    _ ≤ C * ((2:ℝ)^(7/2:ℝ)*(1+‖x‖)^(-(7/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (rate_le_japanese (hL.trans hx.le)) hC
    _ = _ := by ring

theorem tail_constraint_integrable {F κ : E → ℝ} {M C L : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 1 ≤ L) (hML : 4*M ≤ L)
    (_hFmeas : Measurable F) (hκmeas : Measurable κ)
    (hF : ∀ x ∈ tailRegion L, |F x| ≤ M)
    (hκ : ∀ x ∈ tailRegion L, |κ x| ≤ C/(‖x‖^3*Real.sqrt ‖x‖)) :
    IntegrableOn κ (tailRegion L) (tailVolume F) := by
  have hn := tail_density_bound hM (zero_lt_one.trans_le hL) hML hF
  have hμ : (tailVolume F).restrict (tailRegion L) ≤
      ENNReal.ofReal (Real.sqrt 2) • volume.restrict (tailRegion L) := by
    rw [tailVolume,restrict_withDensity (tailRegion_measurable L),← withDensity_const]
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict (tailRegion_measurable L)] with x hx
    exact ENNReal.ofReal_le_ofReal (hn x hx).2.2
  exact ((constraint_integrable_dx hC hL hκmeas hκ).smul_measure ENNReal.ofReal_ne_top).mono_measure hμ
end
end CKSTailVolume

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry MeasureTheory

def spatialMomentum (A B : SpatialTensor) (x : E) : Fin 3 → ℝ :=
  (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x)).momentum
    (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))

def spatialVolume (A : SpatialTensor) : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt (spatialCartesian A x).det))
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
theorem local_coordinate_energy_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    (physicalMetricJet (coordinatePullback e G) x).energy
      (physicalTensorJet (coordinatePullback e K) x) =
    (physicalMetricJet G (e x)).energy (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkSymm := coordinatePullback_symmetric hs
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  have hδ : physicalEnergy (coordinatePullback e G) (coordinatePullback e K)
      (coordinatePullbackFrame e E) x = physicalEnergy G K E (e x) := by
    rw [actualFrameEnergy_coordinate_general hc.target hkSymm,
      actualFrameEnergy_coordinate_general hc.source hs] at hC
    exact hC
  rw [physicalMetricJet_energy hc.target.metric_smooth hc.target.frame_smooth
      hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    physicalMetricJet_energy hc.source.metric_smooth hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal] at hδ
  exact hδ
theorem local_coordinate_energy_pushforward
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt (coordinatePullback e G) E y)
    (hK : ContDiffAt ℝ ∞ (coordinatePullback e K) x)
    (hs : (coordinatePullback e K x).IsHermitian) :
    (physicalMetricJet G (e x)).energy (physicalTensorJet K (e x)) =
    (physicalMetricJet (coordinatePullback e G) x).energy
      (physicalTensorJet (coordinatePullback e K) x) := by
  have hEq (A : PhysicalPoint → AmbientMat) :
      coordinatePullback e.symm (coordinatePullback e A) =ᶠ[𝓝 (e x)] A := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),hi,
      (e.symm.continuousAt (e.map_source hx)).eventually (e.left_inv hx ▸ he)] with y hy hiy hey
    have hh := coordinatePullback_symm e A (e.map_target hy)
      (hey.differentiableAt (by simp)) (by simpa only [e.right_inv hy] using hiy.differentiableAt (by simp))
    simpa only [e.right_inv hy] using hh
  have h := local_coordinate_energy_pullback e.symm (coordinatePullback e G)
    (coordinatePullback e K) E (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he)
    (by simpa only [e.left_inv hx] using hE)
    (by simpa only [e.left_inv hx] using hK)
    (by simpa only [e.left_inv hx] using hs)
  rw [physicalMetricJet_congr (hEq G),physicalTensorJet_congr (hEq K),e.left_inv hx] at h
  exact h
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spherical_physical_energy (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : PhysicalPoint} (hx : 0<x 0) (hs : Real.sin (x 1)≠0)
    (hp : 0<radicand f₀ m R (toPoint.symm (sphericalMap x))) :
    (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x)).energy
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) =
    (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x).energy
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  have hF (y : PhysicalPoint) (hy : 0<y 0) :=
    (outerMass_smooth f₀ hf₀ m hR).contDiffAt (positiveChart_open.mem_nhds hy)
  have hv (y : PhysicalPoint) (hy : 0<y 0) :=
    (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hpx : 0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) x :=
    sphericalMap_radicand f₀ m R hx ▸ hp
  have hreg : ∀ᶠ y in 𝓝 x, 0<y 0 ∧ Real.sin (y 1)≠0 ∧
      0<CKSRealizedRound.radicand (outerMass f₀ m R) (bendingV R) y := by
    filter_upwards [(coord 0).continuous.continuousAt (x := x) |>.eventually (isOpen_Ioi.mem_nhds hx),
      (Real.continuous_sin.comp (coord 1).continuous).continuousAt (x := x) |>.eventually_ne hs,
      (contDiffAt_radicand (hF x hx) (hv x hx) hx.ne').continuousAt.eventually (isOpen_Ioi.mem_nhds hpx)]
      with y hy hsy hpy
    exact ⟨hy,hsy,hpy⟩
  have hEqG : coordinatePullback sphericalMap (physicalMetric f₀ m R) =ᶠ[𝓝 x]
      outerMetric (outerMass f₀ m R) (bendingV R) := by
    filter_upwards [hreg] with y hy
    exact spherical_metric_pullback f₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  have hEqK : coordinatePullback sphericalMap (physicalTensor f₀ m R) =ᶠ[𝓝 x]
      outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R) (outerA f₀ R) (outerPhi f₀ R) := by
    filter_upwards [hreg] with y hy
    exact spherical_tensor_pullback f₀ hf₀ m R hy.1 ((sphericalMap_radicand f₀ m R hy.1).symm ▸ hy.2.2)
  let frame : LocalFrame := fun i y => adaptedFrame
    (lapse (outerMass f₀ m R) (bendingV R) y) (y 0^2 • sphericalAngularMetric y) 0 i
  have hFrame : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt
      (coordinatePullback sphericalMap (physicalMetric f₀ m R)) frame y := by
    filter_upwards [hreg,hEqG.eventually_nhds] with y hy heq
    exact (round_smoothOrthonormalAt (hF y hy.1) (hv y hy.1) hy.1.ne' hy.2.1 hy.2.2).congr_metric heq
  have ha := (outerA_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hb := (outerPhi_smooth f₀ hf₀ hR).contDiffAt (positiveChart_open.mem_nhds hx)
  have hK := (outerTensor_contDiffAt (hF x hx) (hv x hx) (bendingBeta_smooth R).contDiffAt ha hb hx.ne' hpx).congr_of_eventuallyEq hEqK
  have hsymm : (coordinatePullback sphericalMap (physicalTensor f₀ m R) x).IsHermitian := by
    rw [hEqK.self_of_nhds]
    exact CKSRealizedRound.tensor_hermitian ..
  have h := local_coordinate_energy_pushforward (sphericalChart x hx.ne' hs)
    (physicalMetric f₀ m R) (physicalTensor f₀ m R) frame
    (sphericalChart_mem x hx.ne' hs) (Eventually.of_forall fun y => sphericalMap_smooth.contDiffAt)
    (sphericalChart_inverse_smooth x hx.ne' hs) hFrame hK hsymm
  change (physicalMetricJet (physicalMetric f₀ m R) (sphericalMap x)).energy
      (physicalTensorJet (physicalTensor f₀ m R) (sphericalMap x)) =
    (physicalMetricJet (coordinatePullback sphericalMap (physicalMetric f₀ m R)) x).energy
      (physicalTensorJet (coordinatePullback sphericalMap (physicalTensor f₀ m R)) x) at h
  rw [physicalMetricJet_congr hEqG,physicalTensorJet_congr hEqK] at h
  exact h
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spherical_energy_bound_extend_poles {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G (sphericalMap x)) (hk : ContDiffAt ℝ ∞ K (sphericalMap x))
    (h0 : (G (sphericalMap x)).det≠0) {b : ℝ}
    (hb : ∀ p : PhysicalPoint, p 0=x 0 → Real.sin (p 1)≠0 →
      |(physicalMetricJet G (sphericalMap p)).energy
        (physicalTensorJet K (sphericalMap p))| ≤ b) :
    |(physicalMetricJet G (sphericalMap x)).energy
      (physicalTensorJet K (sphericalMap x))| ≤ b := by
  by_cases hs : Real.sin (x 1)≠0
  · exact hb x rfl hs
  · obtain ⟨u,hu,hreg⟩ := regular_angular_approximation x (not_ne_iff.mp hs)
    have hc := ((physicalMetricJet_continuousAt hg h0).energy
      (physicalTensorJet_continuousAt hk)).abs
    exact le_of_tendsto (hc.tendsto.comp (sphericalMap_smooth.continuous.continuousAt.tendsto.comp hu))
      (Eventually.of_forall fun n => hb (u n) (hreg n).1 (hreg n).2)

theorem constructed_cartesian_energy_tail_bound (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ C : ℝ, 12 ≤ R₀ ∧ 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ∀ y : E,
      2*R^2 < ‖y‖ →
      |(physicalMetricJet (physicalMetric f₀ m R) (toPoint y)).energy
        (physicalTensorJet (physicalTensor f₀ m R) (toPoint y))| ≤
        C/(‖y‖^3*Real.sqrt ‖y‖) := by
  obtain ⟨R₁,hR₁,hpos⟩ := cartesian_radicand_positive f₀ hf₀ m
  obtain ⟨R₂,C,hR₂,hC,hbound⟩ := constructed_energy_tail_bound f₀ hf₀ m
  refine ⟨max R₁ R₂,C,hR₁.trans (le_max_left _ _),hC,?_⟩
  intro R hR y hy
  have hRR₁ : R₁≤R := (le_max_left _ _).trans hR
  have hRR₂ : R₂≤R := (le_max_right _ _).trans hR
  have hR12 : 12≤R := hR₁.trans hRR₁
  have hRp : 0<R := by linarith
  have hy3 : 3*R≤‖y‖ := by nlinarith
  have hyp : y≠0 := norm_pos_iff.mp (by linarith : 0<‖y‖)
  obtain ⟨x,hxr,hx⟩ := sphericalMap_surjective_radial y
  have hpx := hpos R hRR₁ y hy3
  have hg : ContDiffAt ℝ ∞ (physicalMetric f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (metric_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  have hk : ContDiffAt ℝ ∞ (physicalTensor f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (tensor_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  rw [←hx]
  apply spherical_energy_bound_extend_poles hg hk
  · change (metric f₀ m R (toPoint.symm (sphericalMap x))).det≠0
    rw [hx,toPoint.symm_apply_apply]
    exact (metric_positive hyp hpx).det_pos.ne'
  · intro p hpr hs
    have hpr' : 0<p 0 := by rw [hpr,hxr]; linarith
    have hprR : 3*R≤p 0 := by rw [hpr,hxr]; exact hy3
    have hp := hpos R hRR₁ (toPoint.symm (sphericalMap p)) (by rwa [sphericalMap_norm hpr'])
    rw [spherical_physical_energy f₀ hf₀ m hRp hpr' hs hp]
    have hb := hbound R hRR₂ p (by rwa [hpr,hxr]) hs
    simpa only [constructedEnergy,constructedTensorJet,hpr,hxr] using hb
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spatialCoefficients_congr {P Q : SpatialTensor} {x : E} (h : P =ᶠ[𝓝 x] Q) :
    spatialCoefficients P =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)] spatialCoefficients Q := by
  have hh := CKSCartesianOuter.toPoint.symm.continuous.continuousAt.eventually
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ h)
  filter_upwards [hh] with y hy
  ext i j
  change P (CKSCartesianOuter.toPoint.symm y) _ _ = Q (CKSCartesianOuter.toPoint.symm y) _ _
  rw [hy]
lemma spatialEnergy_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) : spatialEnergy A B x = spatialEnergy C D x := by
  unfold spatialEnergy
  rw [physicalMetricJet_congr (spatialCoefficients_congr hA),physicalTensorJet_congr (spatialCoefficients_congr hB)]
lemma SourceCollarAtlas.replacement_outer_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖) :
    ∀ᶠ z in 𝓝 x,
      q.replacementMetric f₀ m R z = spatialMatrix (CKSCartesianOuter.metric f₀ m R) z ∧
      q.replacementTensor f₀ m R z = spatialMatrix (CKSCartesianOuter.tensor f₀ m R) z := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
  simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
    ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
  exact ⟨trivial,trivial⟩
lemma SourceCollarAtlas.replacement_outer_energy {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖) :
    spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x =
      (physicalMetricJet (CKSCartesianOuter.physicalMetric f₀ m R) (CKSCartesianOuter.toPoint x)).energy
        (physicalTensorJet (CKSCartesianOuter.physicalTensor f₀ m R) (CKSCartesianOuter.toPoint x)) := by
  have h := q.replacement_outer_eventually f₀ m hR hx
  rw [spatialEnergy_congr (h.mono fun _ hh => hh.1) (h.mono fun _ hh => hh.2)]
  unfold spatialEnergy
  rw [spatialCoefficients_spatialMatrix,spatialCoefficients_spatialMatrix]
  rfl
lemma SourceCollarAtlas.replacement_momentum_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    spatialMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x = 0 := by
  have hk : q.replacementTensor f₀ m R =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
    exact (q.replacement_tail f₀ m hR hz).2
  unfold spatialMomentum
  rw [physicalTensorJet_congr (spatialCoefficients_congr hk)]
  ext i
  simp [CKSRound.MetricJet.momentum,CKSRound.MetricJet.tensorDivergence,CKSRound.MetricJet.dTrace,
    physicalTensorJet,spatialCoefficients,CKSCalculus.D]
lemma SourceCollarAtlas.replacement_density_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    Real.sqrt (spatialCartesian (q.replacementMetric f₀ m R) x).det =
      CKSTailVolume.density (cartMass f₀ m R) x := by
  rw [(q.replacement_tail f₀ m hR hx).1]
  have he : CKSADM.metric (cartB f₀ m R) x = CKSTailVolume.tailMetric (cartMass f₀ m R) x := by
    ext i j
    simp only [CKSADM.metric,cartB,normal,CKSTailVolume.tailMetric,CKSTailVolume.direction,
      Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    ring
  rw [he]
  rfl

lemma SourceCollarAtlas.replacement_energy_continuousAt {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖)
    (hg : ContDiffAt ℝ ∞ (CKSCartesianOuter.metric f₀ m R) x)
    (hk : ContDiffAt ℝ ∞ (CKSCartesianOuter.tensor f₀ m R) x)
    (hp : (CKSCartesianOuter.metric f₀ m R x).PosDef) :
    ContinuousAt (spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R)) x := by
  have hgg : ContDiffAt ℝ ∞ (CKSCartesianOuter.physicalMetric f₀ m R) (CKSCartesianOuter.toPoint x) :=
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ hg).comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  have hkk : ContDiffAt ℝ ∞ (CKSCartesianOuter.physicalTensor f₀ m R) (CKSCartesianOuter.toPoint x) :=
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ hk).comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  have hdet : (CKSCartesianOuter.physicalMetric f₀ m R (CKSCartesianOuter.toPoint x)).det ≠ 0 := by
    simpa [CKSCartesianOuter.physicalMetric] using hp.det_pos.ne'
  have hc := ((physicalMetricJet_continuousAt hgg hdet).energy (physicalTensorJet_continuousAt hkk)).comp
    CKSCartesianOuter.toPoint.continuous.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
  exact q.replacement_outer_energy f₀ m hR hz
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

theorem actual_same_end_tail_integrable {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∃ L : ℝ, 2*R^2 ≤ L ∧
      IntegrableOn (spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R))
        (CKSTailVolume.tailRegion L) (spatialVolume (q.replacementMetric f₀ m R)) ∧
      ∀ x : E, 2*R^2 < ‖x‖ →
        spatialMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x = 0 := by
  obtain ⟨R₁,C,hR₁,hC,hbound⟩ := CKSCartesianOuter.constructed_cartesian_energy_tail_bound f₀ hf₀ m
  obtain ⟨R₂,hR₂,hreg⟩ := CKSCartesianOuter.constructed_cartesian_outer_regular f₀ hf₀ m
  obtain ⟨M,hM,hF⟩ := CKSCartesianOuter.cartMass_uniform_bound f₀ hf₀ m
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),?_⟩
  intro R hR
  have h1 : R₁ ≤ R := (le_max_left _ _).trans hR
  have h2 : R₂ ≤ R := (le_max_right _ _).trans hR
  have hR12 : 12 ≤ R := hR₁.trans h1
  have hRp : 0 ≤ R := by linarith
  let L := max (2*R^2) (4*M+1)
  have hL : 1 ≤ L := le_trans (by linarith) (le_max_right _ _)
  have hML : 4*M ≤ L := le_trans (by linarith) (le_max_right _ _)
  have hRL : 2*R^2 ≤ L := le_max_left _ _
  let κ := spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R)
  have hr (x : E) (hx : x ∈ CKSTailVolume.tailRegion L) : 2*R^2 < ‖x‖ := hRL.trans_lt hx
  have hr3 (x : E) (hx : x ∈ CKSTailVolume.tailRegion L) : 3*R < ‖x‖ := by
    have hh := hr x hx
    nlinarith
  have hκ : ∀ x ∈ CKSTailVolume.tailRegion L, |κ x| ≤ C/(‖x‖^3*Real.sqrt ‖x‖) := by
    intro x hx
    dsimp [κ]
    rw [q.replacement_outer_energy f₀ m hRp (hr3 x hx)]
    exact hbound R h1 x (hr x hx)
  have hcont : ContinuousOn κ (CKSTailVolume.tailRegion L) := by
    intro x hx
    obtain ⟨hg,hk,hp,hs⟩ := hreg R h2 x (hr3 x hx).le
    exact (q.replacement_energy_continuousAt f₀ m hRp (hr3 x hx) hg hk hp).continuousWithinAt
  have hdx : IntegrableOn κ (CKSTailVolume.tailRegion L) volume := by
    have hh : Integrable (fun x : E => (1+‖x‖)^(-(7/2:ℝ))) volume :=
      integrable_one_add_norm (by norm_num [E,finrank_euclideanSpace])
    apply ((hh.const_mul (C*(2:ℝ)^(7/2:ℝ))).integrableOn).mono'
      (hcont.aestronglyMeasurable (CKSTailVolume.tailRegion_measurable L))
    filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable L)] with x hx
    rw [Real.norm_eq_abs]
    calc
      _ ≤ C/(‖x‖^3*Real.sqrt ‖x‖) := hκ x hx
      _ = C * (1/(‖x‖^3*Real.sqrt ‖x‖)) := by ring
      _ ≤ C * ((2:ℝ)^(7/2:ℝ)*(1+‖x‖)^(-(7/2:ℝ))) :=
        mul_le_mul_of_nonneg_left (CKSTailVolume.rate_le_japanese (hL.trans hx.le)) hC
      _ = _ := by ring
  have hden := CKSTailVolume.tail_density_bound hM.le (zero_lt_one.trans_le hL) hML
    (fun x hx => hF R (by linarith : 1 ≤ R) x (hr3 x hx).le)
  have hμ : (spatialVolume (q.replacementMetric f₀ m R)).restrict (CKSTailVolume.tailRegion L) ≤
      ENNReal.ofReal (Real.sqrt 2) • volume.restrict (CKSTailVolume.tailRegion L) := by
    rw [spatialVolume,restrict_withDensity (CKSTailVolume.tailRegion_measurable L),← withDensity_const]
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable L)] with x hx
    apply ENNReal.ofReal_le_ofReal
    rw [q.replacement_density_tail f₀ m hR12 (hr x hx)]
    exact (hden x hx).2.2
  exact ⟨L,hRL,(hdx.smul_measure ENNReal.ofReal_ne_top).mono_measure hμ,
    fun x hx => q.replacement_momentum_tail f₀ m hR12 hx⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSBending Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma cartesian_metric_polar_block (P : SmoothAngularPatch) (f₀ : C(Sphere,ℝ)) (m R : ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) i j y) =
      metricBlock (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) := by
  simpa only [one_mul] using radial_matrix_polar P (CKSCartesianOuter.metric f₀ m R)
    (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 1 hr hy (by simp [CKSCartesianOuter.metric])
lemma generic_outer_background_lower (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R ≥ R₀, 0 < l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ (P : SmoothAngularPatch) (y : CKSMixedGeometry.Point),
        3*R ≤ y 0 → angularProjection y ∈ P.chart.target →
        ∀ v : Fin 3 → ℝ,
          l R * quadratic3 (metricBlock 1 0 (angularRoundMetric P.param (angularProjection y))) v ≤
          quadratic3 (radialNormalize (y 0) (fun i j => polarTensorComponents P
            (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) i j y)) v := by
  obtain ⟨M,hM,hbound⟩ := CKSCartesianOuter.cartMass_uniform_bound f₀ hf₀ m
  refine ⟨max 12 (4*M),le_max_left _ _,outerComparisonFactor M,
    outerComparisonFactor_tendsto M,?_,?_⟩
  · intro R hR
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) ((le_max_left _ _).trans hR)
    exact ⟨outerComparisonFactor_pos hM.le hRp,outerComparisonFactor_le_one hM.le hRp⟩
  intro R hR P y hr hy
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRM : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hmass := hbound R (by linarith) (polarParam P y) (by rwa [polarParam_norm P hrp.le])
  have hp := outer_radicand_positive hrp hmass (by linarith : 4*M ≤ y 0) (v := bendingV R (y 0))
  rw [cartesian_metric_polar_block P f₀ m R hrp hy]
  have he : metricBlock (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
      (y 0^2 • angularRoundMetric P.param (angularProjection y)) =
      foliationMetric (Real.sqrt (1+bendingV R (y 0)^2-2*CKSADM.cartMass f₀ m R (polarParam P y)/(y 0)))
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) 0 := by
    rw [foliationMetric]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero,
      CKSCartesianOuter.radicand,polarParam_norm P hrp.le,Real.sq_sqrt hp.le,one_div]
    rfl
  rw [he]
  exact outer_metric_lower (by linarith) (by linarith) hM.le hmass
    (bendingV_nonneg hRp hrp) (bendingV_le_radius hRp hrp) hp (P.roundMetric_posDef hy)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma SourceCollarAtlas.eventually_outer_local_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ i y, 3*R ≤ y 0 → angularProjection y ∈ (q.patch i).region →
        ∀ v : Fin 3 → ℝ,
        l R * quadratic3 (sourceMetric (q.patch i).fields.base y) v ≤
          quadratic3 (fun a b => polarTensorComponents (q.patch i).patch
            (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) a b y) v := by
  obtain ⟨R₁,hR₁,l,hl,hlb,houter⟩ := generic_outer_background_lower f₀ hf₀ m
  let val : CKSMixedGeometry.MatrixThreeJet → CKSAngularGeometry.Mat := fun q i j => (q i j).1.1
  have hv : Continuous val := by unfold val; fun_prop
  obtain ⟨κ,hκ,hlower⟩ := compact_background_lower (q.jetSet_compact.image hv)
    (by rintro _ ⟨d,hd,rfl⟩; exact q.jetSet_positive d hd)
  refine ⟨max R₁ (q.radius+1),hR₁.trans (le_max_left _ _),
    lt_of_lt_of_le (by linarith) (le_max_right _ _),fun R => l R*comparisonFactor 0 q.bound κ R,?_,?_,?_⟩
  · simpa only [mul_one] using hl.mul (comparisonFactor_tendsto 0 q.bound κ)
  · intro R hR
    have h1 := (le_max_left R₁ (q.radius+1)).trans hR
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) (hR₁.trans h1)
    have hn := comparisonFactor_nonneg q.bound_nonneg hκ hRp
      (by simpa only [mul_zero] using (mul_nonneg hκ.le (pow_nonneg hRp.le 3)) : 3*(0:ℝ) ≤ κ*R^3)
    have ht := comparisonFactor_le_one (le_refl (0:ℝ)) q.bound_nonneg hκ hRp
    exact ⟨mul_nonneg (hlb R h1).1.le hn,
      (mul_le_mul_of_nonneg_left ht (hlb R h1).1.le).trans (by simpa using (hlb R h1).2)⟩
  intro R hR i y hr hw
  have h1 := (le_max_left R₁ (q.radius+1)).trans hR
  have hR12 : 12 ≤ R := hR₁.trans h1
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hqr : q.radius < y 0 := by have := (le_max_right R₁ (q.radius+1)).trans hR; linarith
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hrp)
  obtain ⟨hm,hσ,hmg,hmk,hmr,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hrp])
  rw [hlog] at hb'
  have hg0 : ‖(q.patch i).fields.base.mg (angularProjection y)‖ ≤ q.bound := by
    simpa only [angularLift,angularProjection_slice] using
      matrixThreeJets_value_bound (q:=angularLift (q.patch i).fields.base.mg)
        (x:=slice (Real.log (y 0)) (angularProjection y)) q.bound_nonneg hmg
  have hmr0 : |(q.patch i).fields.base.mr (angularProjection y)| ≤ q.bound := by
    simpa only [angularLift,angularProjection_slice] using
      actualScalarJet_value_bound (q:=angularLift (q.patch i).fields.base.mr)
        (x:=slice (Real.log (y 0)) (angularProjection y)) hmr
  have hg := originalMetric_error (f:=(q.patch i).fields.base) (y:=y)
    (by linarith) q.bound_nonneg hmr0 hg0 hb'.base
  have hbase : ∀ v : Fin 3 → ℝ, κ*(∑ j, (v j)^2) ≤
      quadratic3 (metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y))) v := by
    have h := hlower _ ⟨_,hm,rfl⟩
    simpa only [val,CKSMixedGeometry.matrixThreeJets,CKSMixedGeometry.actualThreeJet,CKSMixedGeometry.actualScalarJet,angularLift,angularProjection_slice] using h
  have hcomp := metric_comparison_uniform (C:=0)
    (G:=metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y)))
    (le_refl (0:ℝ)) q.bound_nonneg hκ hRp (by linarith : R ≤ y 0)
    (by simpa only [mul_zero] using (mul_nonneg hκ.le (pow_nonneg hRp.le 3)) : 3*(0:ℝ) ≤ κ*R^3)
    (by simp) hg hbase
  have hout := houter R h1 (q.patch i).patch y hr ((q.patch i).region_target hw)
  apply radialNormalize_comparison hrp.ne'
  intro v
  calc
    (l R*comparisonFactor 0 q.bound κ R)*quadratic3 (radialNormalize (y 0)
        (sourceMetric (q.patch i).fields.base y)) v =
      l R*(comparisonFactor 0 q.bound κ R*quadratic3 (radialNormalize (y 0)
        (sourceMetric (q.patch i).fields.base y)) v) := by ring
    _ ≤ l R*quadratic3 (metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y))) v :=
      mul_le_mul_of_nonneg_left (hcomp v) (hlb R h1).1.le
    _ ≤ _ := hout v
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma polar_spatial_quadratic (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (v : E) :
    A (polarParam P y) v v = quadratic3 (fun i j => polarTensorComponents P A i j y)
      (fderiv ℝ (polarInverse P) (polarParam P y) v) := by
  have he := (polarLift_reconstruction P (fun z i j => polarTensorComponents P A i j z) hr hy).2 A
    (fun _ _ => rfl)
  exact (congrArg (fun a : SpatialBilinear => a v v) he).symm.trans
    (polarLift_quadratic P (fun z i j => polarTensorComponents P A i j z) hr hy v)
lemma SourceCollarAtlas.eventually_outer_spatial_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ x : E, 3*R ≤ ‖x‖ → ∀ v : E,
        l R * sourceSpatial A x v v ≤ spatialMatrix (CKSCartesianOuter.metric f₀ m R) x v v := by
  obtain ⟨R₀,hR₀,hq₀,l,hl,hlb,hcomp⟩ := q.eventually_outer_local_lower f₀ hf₀ m
  refine ⟨R₀,hR₀,hq₀,l,hl,hlb,?_⟩
  intro R hR x hx v
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) (hR₀.trans hR)
  have hqx : q.radius < ‖x‖ := lt_of_lt_of_le (hq₀.trans_le hR) (by linarith)
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (by linarith : 0 < ‖x‖),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hrec := spatial_source_reconstruction (q.patch i) hy0 hyt
    (by rw [hyx]; exact hA x hqx) (by rw [hyx]; exact hB x hqx)
  have h := hcomp R hR i y (by rwa [hyr]) hyw
    (fderiv ℝ (polarInverse (q.patch i).patch) x v)
  rw [← hyx,← hrec.2.2.1,polarLift_quadratic _ _ hy0 hyt,
    polar_spatial_quadratic _ _ hy0 hyt]
  simpa only [hyx] using h
lemma SourceCollarAtlas.eventually_closed_collar_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 3*R → ∀ v : E,
        l R * sourceSpatial A x v v ≤ q.metric R x v v := by
  obtain ⟨R₁,hR₁,hq₁,l,hl,hlb,hcomp⟩ := q.eventually_local_lower
  obtain ⟨R₂,hR₂,hq₂,hreg⟩ := q.eventually_pointwise
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),hq₁.trans_le (le_max_left _ _),l,hl,?_,?_⟩
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R hR x hr ht v
  have hR1 := (le_max_left R₁ R₂).trans hR
  have hR2 := (le_max_right R₁ R₂).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)
  have hqx : q.radius < ‖x‖ := (hq₁.trans_le hR1).trans_le hr
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (hRpos.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
  let y := polarInverse (q.patch i).patch x
  have hrec := spatial_source_reconstruction (q.patch i) hy hyt
    (by rw [hyx]; exact hA x hqx) (by rw [hyx]; exact hB x hqx)
  have hg := (q.local_eq hRpos (hq₂.trans_le hR2)
    (fun i y hr ht hw => (hreg R hR2 i y hr ht hw).1) hr ht hc).1
  have hlower := hcomp R hR1 i y (by dsimp [y]; rw [hyr]; exact hr)
    (by dsimp [y]; rw [hyr]; exact ht) hyw (fderiv ℝ (polarInverse (q.patch i).patch) x v)
  rw [hg,← hyx,← hrec.2.2.1,polarLift_quadratic _ _ hy hyt]
  change _ ≤ polarLift (q.patch i).patch _ (polarParam (q.patch i).patch y) v v
  rw [polarLift_quadratic _ _ hy hyt]
  simpa only [hyx] using hlower
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem actual_same_end_uniform_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ ε : ℝ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ R ≥ R₀, 0 ≤ ε R ∧ ε R < 1) ∧
      ∀ R ≥ R₀, ∀ x : E, q.radius < ‖x‖ → ∀ v : E,
        (1-ε R)*sourceSpatial A x v v ≤ q.replacementMetric f₀ m R x v v := by
  obtain ⟨R₁,hR₁,hq₁,l₁,hl₁,hb₁,hc⟩ := q.eventually_closed_collar_lower hA hB
  obtain ⟨R₂,hR₂,hq₂,l₂,hl₂,hb₂,ho⟩ := q.eventually_outer_spatial_lower f₀ hf₀ m hA hB
  let l := fun R => min (l₁ R) (l₂ R)
  have hl : Tendsto l atTop (𝓝 1) := by simpa [l] using hl₁.min hl₂
  obtain ⟨R₃,h₃⟩ := eventually_atTop.mp (hl.eventually (Ioi_mem_nhds (zero_lt_one : (0:ℝ)<1)))
  let R₀ := max (max R₁ R₂) R₃
  have h01 : R₁ ≤ R₀ := (le_max_left R₁ R₂).trans (le_max_left _ _)
  have h02 : R₂ ≤ R₀ := (le_max_right R₁ R₂).trans (le_max_left _ _)
  have h03 : R₃ ≤ R₀ := le_max_right _ _
  refine ⟨R₀,hR₂.trans h02,hq₂.trans_le h02,fun R => 1-l R,?_,?_,?_⟩
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hl
  · intro R hR
    have ht : l R ≤ 1 := (min_le_left _ _).trans (hb₁ R (h01.trans hR)).2
    have hp := h₃ R (h03.trans hR)
    exact ⟨sub_nonneg.mpr ht,by linarith⟩
  intro R hR x hx v
  have hg : 0 ≤ sourceSpatial A x v v := by
    by_cases hv : v=0
    · simp [hv]
    · exact (q.source_spatial_regular hA hB hx).2.2.2.1 v hv |>.le
  have hl1 : l R ≤ l₁ R := min_le_left _ _
  have hl2 : l R ≤ l₂ R := min_le_right _ _
  simp only [sub_sub_cancel]
  unfold SourceCollarAtlas.replacementMetric
  split_ifs with hr ht
  · exact (mul_le_mul_of_nonneg_right
      (hl1.trans (hb₁ R (h01.trans hR)).2) hg).trans_eq (one_mul _)
  · exact (mul_le_mul_of_nonneg_right hl1 hg).trans
      (hc R (h01.trans hR) x (le_of_not_ge hr) ht v)
  · exact (mul_le_mul_of_nonneg_right hl2 hg).trans
      (ho R (h02.trans hR) x (le_of_not_ge ht) v)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_CKS_end_replacement {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      1 ≤ T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x : E, T < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ContDiffOn ℝ ∞ (G R) {x | T < ‖x‖} ∧
        ContDiffOn ℝ ∞ (k R) {x | T < ‖x‖} ∧
        (∀ x, T < ‖x‖ →
          (∀ v w, G R x v w = G R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < G R x v v) ∧
          (∀ v w, k R x v w = k R x w v) ∧
          spatialDEC (G R) (k R) x ∧
          ∀ v : E, (1-ε R)*sourceSpatial A' x v v ≤ G R x v v) ∧
        (∀ x, ‖x‖ ≤ R → G R x = sourceSpatial A' x ∧ k R x = sourceSpatial B' x) ∧
        (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
        (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
        Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
        Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
        0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
        (∃ L : ℝ, 2*R^2 ≤ L ∧
          IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion L) (spatialVolume (G R))) ∧
        ∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0 := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
  obtain ⟨ι,q,hM',hne,hmass,hcharge,hheat,hbalanced,hfar⟩ :=
    source_atlas_from_original hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  have hA' (x : E) (hx : q.radius < ‖x‖) (v w : E) : A' x v w = A' x w v :=
    hA _ (hfar x hx) _ _
  have hB' (x : E) (hx : q.radius < ‖x‖) (v w : E) : B' x v w = B' x w v :=
    hB _ (hfar x hx) _ _
  let f := heatDatum (aspectPullback e p ht M) hM'
  let m := mass e p
  obtain ⟨S₁,R₁,hS₁,hq₁,h₁,hsm⟩ :=
    actual_same_end_smooth_replacement q hM' hmass m hcharge hA' hB'
  obtain ⟨S₂,R₂,hS₂,hq₂,h₂,hdec⟩ := actual_same_end_DEC q hM' hmass m hcharge hA' hB'
  obtain ⟨R₃,hR₃,hq₃,ε,hε,hεb,hlower⟩ := actual_same_end_uniform_lower q f hheat m hA' hB'
  obtain ⟨R₄,hR₄,hint⟩ := actual_same_end_tail_integrable q f hheat m
  let T := max S₁ S₂
  let R₀ := max (T+1) (max (max R₁ R₂) (max R₃ R₄))
  have h1 : R₁ ≤ R₀ := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h2 : R₂ ≤ R₀ := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h3 : R₃ ≤ R₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : R₄ ≤ R₀ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs1 : S₁ ≤ T := le_max_left _ _
  have hs2 : S₂ ≤ T := le_max_right _ _
  have hqt : q.radius < T := hq₁.trans_le hs1
  refine ⟨T,R₀,ε,q.replacementMetric f m,q.replacementTensor f m,
    hS₁.trans hs1,lt_of_lt_of_le (by linarith : T < T+1) (le_max_left _ _),
    hR₃.trans h3,hε,fun x hx => hfar x (hqt.trans hx),?_⟩
  intro R hR
  obtain ⟨hg,hk,hpk,heq,_,_⟩ := hsm R (h1.trans hR)
  obtain ⟨hz,haf,hE,hP,hη0,hη1⟩ := actual_same_end_AF_ADM q f hheat m ((hR₃.trans h3).trans hR)
  obtain ⟨L,hL,hint',hmom⟩ := hint R (h4.trans hR)
  refine ⟨hεb R (h3.trans hR),hg.mono (fun x hx => hs1.trans_lt hx),
    hk.mono (fun x hx => hs1.trans_lt hx),?_,heq,hz,haf,hE,hP,hη0,hη1,⟨L,hL,hint'⟩,hmom⟩
  intro x hx
  obtain ⟨hgs,hgp,hks⟩ := hpk x (hs1.trans_lt hx)
  exact ⟨hgs,hgp,hks,hdec R (h2.trans hR) x (hs2.trans_lt hx),hlower R (h3.trans hR) x (hqt.trans hx)⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
lemma spatial_energy_continuousAt {A B : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hsym : ∀ v w, A x v w = A x w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ContinuousAt (spatialEnergy A B) x := by
  have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth hA)
    (spatialCoefficients_positive hsym hpos).det_pos.ne'
  have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth hB)
  exact (hg.energy hk).comp CKSCartesianOuter.toPoint.continuous.continuousAt
lemma spatial_density_continuousAt {A : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) :
    ContinuousAt (fun y => Real.sqrt (spatialCartesian A y).det) x := by
  have hc : ContinuousAt (spatialCartesian A) x :=
    (spatialCoefficients_smooth hA).continuousAt.comp CKSCartesianOuter.toPoint.continuous.continuousAt
  exact (((continuous_id : Continuous (fun M : AmbientMat => M)).matrix_det).continuousAt.comp hc).sqrt
lemma spatial_integrableOn_compact {A : SpatialTensor} {f : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x)
    (hf : ContinuousOn f K) : IntegrableOn f K (spatialVolume A) := by
  have hd : ContinuousOn (fun x => Real.sqrt (spatialCartesian A x).det) K :=
    fun x hx => (spatial_density_continuousAt (hA x hx)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hd
  have hμ : (spatialVolume A).restrict K ≤ ENNReal.ofReal C • volume.restrict K := by
    rw [spatialVolume,restrict_withDensity hK.measurableSet,← withDensity_const]
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with x hx
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)
  exact ((hf.integrableOn_compact hK).smul_measure ENNReal.ofReal_ne_top).mono_measure hμ

theorem end_constraints_integrable {A B : SpatialTensor} {T L s : ℝ}
    (hA : ContDiffOn ℝ ∞ A {x | T < ‖x‖})
    (hB : ContDiffOn ℝ ∞ B {x | T < ‖x‖})
    (hsym : ∀ x, T < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < A x v v)
    (hDEC : ∀ x, T < ‖x‖ → spatialDEC A B x)
    (htail : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion L) (spatialVolume A))
    (hs : T < s) :
    IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A) ∧
    IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
      (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x))
      (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))))
      (CKSTailVolume.tailRegion s) (spatialVolume A) := by
  have ho : IsOpen {x : E | T < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have ha (x : E) (hx : T < ‖x‖) := hA.contDiffAt (ho.mem_nhds hx)
  have hb (x : E) (hx : T < ‖x‖) := hB.contDiffAt (ho.mem_nhds hx)
  let K : Set E := {x | s ≤ ‖x‖ ∧ ‖x‖ ≤ L}
  have hK : IsCompact K := by
    have he : K = Metric.closedBall (0:E) L ∩ {x | s ≤ ‖x‖} := by
      ext x
      simp only [K,mem_ofPred_eq,mem_inter_iff,Metric.mem_closedBall,dist_zero_right]
      tauto
    rw [he]
    exact (isCompact_closedBall (0:E) L).inter_right (isClosed_le continuous_const continuous_norm)
  have hkt (x : E) (hx : x ∈ K) : T < ‖x‖ := hs.trans_le hx.1
  have hiK : IntegrableOn (spatialEnergy A B) K (spatialVolume A) :=
    spatial_integrableOn_compact hK (fun x hx => ha x (hkt x hx)) fun x hx =>
      (spatial_energy_continuousAt (ha x (hkt x hx)) (hb x (hkt x hx))
        (hsym x (hkt x hx)) (hpos x (hkt x hx))).continuousWithinAt
  have hie : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A) := by
    apply (hiK.union htail).mono_set
    intro x hx
    by_cases hL : L < ‖x‖
    · exact Or.inr hL
    · exact Or.inl ⟨hx.le,le_of_not_gt hL⟩
  refine ⟨hie,?_⟩
  have hc : ContinuousOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
      (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x))
      (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))))
      (CKSTailVolume.tailRegion s) := by
    intro x hx
    have hxt : T < ‖x‖ := hs.trans hx
    have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth (ha x hxt))
      (spatialCoefficients_positive (hsym x hxt) (hpos x hxt)).det_pos.ne'
    have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth (hb x hxt))
    exact ((hg.momentumSq hk).sqrt.comp CKSCartesianOuter.toPoint.continuous.continuousAt).continuousWithinAt
  apply hie.mono' (hc.aestronglyMeasurable (CKSTailVolume.tailRegion_measurable s))
  filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable s)] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hDEC x (hs.trans hx)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_CKS_end_integrable_replacement {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      1 ≤ T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x : E, T < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ContDiffOn ℝ ∞ (G R) {x | T < ‖x‖} ∧
        ContDiffOn ℝ ∞ (k R) {x | T < ‖x‖} ∧
        (∀ x, T < ‖x‖ →
          (∀ v w, G R x v w = G R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < G R x v v) ∧
          (∀ v w, k R x v w = k R x w v) ∧
          spatialDEC (G R) (k R) x ∧
          ∀ v : E, (1-ε R)*sourceSpatial A' x v v ≤ G R x v v) ∧
        (∀ x, ‖x‖ ≤ R → G R x = sourceSpatial A' x ∧ k R x = sourceSpatial B' x) ∧
        (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
        (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
        Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
        Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
        0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
        (∀ s : ℝ, T < s →
          IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
          IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
            (physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
            (physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
            (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
        ∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0 := by
  classical
  dsimp only
  obtain ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hfar,hall⟩ :=
    original_CKS_end_replacement hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  refine ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hfar,?_⟩
  intro R hR
  obtain ⟨heps,hGs,hks,hgeom,heq,hzero,hAF,hE,hP,hpad0,hpad1,⟨L,hL,hi⟩,hmom⟩ := hall R hR
  refine ⟨heps,hGs,hks,hgeom,heq,hzero,hAF,hE,hP,hpad0,hpad1,?_,hmom⟩
  intro s hs
  exact end_constraints_integrable hGs hks (fun x hx => (hgeom x hx).1)
    (fun x hx => (hgeom x hx).2.1) (fun x hx => (hgeom x hx).2.2.2.1) hi hs
end
end CKSLorentz

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

theorem boosted_end_proper (h : E ≃ₜ E) (f : M → E) {U : Set M}
    (hU : IsOpen U) (hf : ContinuousOn f U) {S : ℝ}
    (hclosed : ∀ r, S < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖}) (T₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ T₀ ≤ T ∧
      (∀ z : E, T < ‖z‖ → S+1 < ‖h z‖) ∧
      IsOpen {x : M | x ∈ U ∧ T < ‖h.symm (f x)‖} ∧
      ∀ r, T < r → IsClosed {x : M |
        (x ∈ U ∧ T < ‖h.symm (f x)‖) ∧ r ≤ ‖h.symm (f x)‖} := by
  obtain ⟨T,hT,hT₀,hfar⟩ := homeomorph_maps_far_tail h (S+1) T₀
  have hnew : ContinuousOn (fun x => ‖h.symm (f x)‖) U :=
    (h.symm.continuous.comp_continuousOn hf).norm
  refine ⟨T,hT,hT₀,hfar,?_,?_⟩
  · exact hnew.isOpen_inter_preimage hU isOpen_Ioi
  · intro r hr
    let C : Set M := {x | x ∈ U ∧ S+1 ≤ ‖f x‖}
    have hC : IsClosed C := hclosed _ (by linarith)
    have hc : ContinuousOn (fun x => ‖h.symm (f x)‖) C :=
      hnew.mono (fun x hx => hx.1)
    have hh := hc.preimage_isClosed_of_isClosed hC (isClosed_Ici : IsClosed (Ici r))
    convert hh using 1
    ext x
    constructor
    · rintro ⟨⟨hx,hTx⟩,hrx⟩
      have hxS := hfar (h.symm (f x)) hTx
      rw [h.apply_symm_apply] at hxS
      exact ⟨⟨hx,hxS.le⟩,hrx⟩
    · rintro ⟨⟨hx,hxS⟩,hrx⟩
      exact ⟨⟨hx,hr.trans_le hrx⟩,hrx⟩
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold
open scoped Bundle Manifold ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
def tangentNorm (g : Metric I (M := M)) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)
def metricEDist (g : Metric I (M := M)) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y
def MetricLower (g G : Metric I (M := M)) (ε : ℝ) : Prop :=
  ∀ x (v : TangentSpace I x), (1-ε) * g.inner x v v ≤ G.inner x v v
end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Filter
open scoped Topology ENNReal

theorem complete_of_emetricLower {X : Type*} (g G : EMetricSpace X)
    (htop : g.toUniformSpace.toTopologicalSpace = G.toUniformSpace.toTopologicalSpace)
    (c : ℝ≥0∞) (hc : 0 < c) (hcfin : c ≠ ⊤)
    (hg : @CompleteSpace X g.toUniformSpace)
    (hlow : ∀ x y, c * @edist X g.toEDist x y ≤ @edist X G.toEDist x y) :
    @CompleteSpace X G.toUniformSpace := by
  refine @CompleteSpace.mk X G.toUniformSpace ?_
  intro f hf
  have hf' : @Cauchy X g.toUniformSpace f := by
    apply (@EMetric.cauchy_iff X g.toPseudoEMetricSpace f).2
    obtain ⟨hne, hsmall⟩ := (@EMetric.cauchy_iff X G.toPseudoEMetricSpace f).1 hf
    refine ⟨hne, fun δ hδ => ?_⟩
    obtain ⟨s, hs, hdist⟩ := hsmall (c * δ) (ENNReal.mul_pos hc.ne' hδ.ne')
    refine ⟨s, hs, fun x hx y hy => ?_⟩
    exact (ENNReal.mul_lt_mul_iff_right hc.ne' hcfin).mp
      ((hlow x y).trans_lt (hdist x hx y hy))
  obtain ⟨x, hx⟩ := @CompleteSpace.complete X g.toUniformSpace hg f hf'
  refine ⟨x, ?_⟩
  rw [← htop]
  exact hx
end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
lemma metricEDist_eq (g : Metric I (M := M)) (x y : M) :
    metricEDist I g x y =
      ⨅ γ : Path x y, ⨅ (_ : ContMDiff (modelWithCornersEuclideanHalfSpace 1) I 1 γ),
        ∫⁻ t : unitInterval, ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  unfold metricEDist
  rw [Manifold.riemannianEDist_def]
  congr 1
  funext γ
  congr 1
  funext hγ
  apply lintegral_congr
  intro t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl
lemma tangentNorm_lower (g G : Metric I (M := M)) {ε : ℝ} (hε : ε < 1)
    (hlow : MetricLower I g G ε) (x : M) (v : TangentSpace I x) :
    Real.sqrt (1-ε) * tangentNorm I g x v ≤ tangentNorm I G x v := by
  unfold tangentNorm
  rw [← Real.sqrt_mul (by linarith : 0 ≤ 1-ε)]
  exact Real.sqrt_le_sqrt (hlow x v)

theorem metricEDist_lower (g G : Metric I (M := M)) {ε : ℝ} (hε : ε < 1)
    (hlow : MetricLower I g G ε) (x y : M) :
    ENNReal.ofReal (Real.sqrt (1-ε)) * metricEDist I g x y ≤ metricEDist I G x y := by
  rw [metricEDist_eq, metricEDist_eq]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (1-ε)) *
        ∫⁻ t : unitInterval, ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) :=
      mul_le_mul' le_rfl (iInf_le_of_le γ (iInf_le _ hγ))
    _ = ∫⁻ t : unitInterval, ENNReal.ofReal (Real.sqrt (1-ε)) *
        ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (1-ε))]
      exact ENNReal.ofReal_le_ofReal (tangentNorm_lower I g G hε hlow _ _)
variable [T3Space M]
lemma metricSpace_topology (g : Metric I (M := M)) :
    (metricSpace I g).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl
lemma metricSpace_edist (g : Metric I (M := M)) (x y : M) :
    @edist M (metricSpace I g).toEDist x y = metricEDist I g x y := rfl

theorem complete_of_metricLower (g G : Metric I (M := M))
    {ε : ℝ} (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hg : IsComplete I g) (hlow : MetricLower I g G ε) : IsComplete I G := by
  have htop : (metricSpace I g).toUniformSpace.toTopologicalSpace =
      (metricSpace I G).toUniformSpace.toTopologicalSpace :=
    (metricSpace_topology I g).trans (metricSpace_topology I G).symm
  have hdist : ∀ x y, ENNReal.ofReal (Real.sqrt (1-ε)) *
      @edist M (metricSpace I g).toEDist x y ≤ @edist M (metricSpace I G).toEDist x y := by
    intro x y
    rw [metricSpace_edist, metricSpace_edist]
    exact metricEDist_lower I g G hε1 hlow x y
  exact complete_of_emetricLower (metricSpace I g) (metricSpace I G) htop
    (ENNReal.ofReal (Real.sqrt (1-ε)))
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hε1)))
    ENNReal.ofReal_ne_top hg hdist

end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory Bundle CKSReplacementCompleteness
open scoped ENNReal Manifold Bundle ContDiff
universe u
def rawHausdorffArea {X : Type u} (metric : EMetricSpace X) (s : Set X) : ℝ≥0∞ :=
  letI : EMetricSpace X := metric
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  (Measure.hausdorffMeasure (2 : ℝ) : Measure X) s
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 1 M]

def OuterDomain.cut (D : OuterDomain M) : Set M :=
  D.inclusion '' (@ModelWithCorners.boundary ℝ _ E3 _ _ H3 _ I3 D.Carrier D.topology D.charts)
def IsEnclosingCut (Γ : Set M) : Prop := ∃ D : OuterDomain M, Γ = D.cut
variable [T3Space M]
def area (g : Metric I3 (M := M)) (Γ : Set M) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi / 4) * rawHausdorffArea (metricSpace I3 g) Γ
def minEnclosingArea (g : Metric I3 (M := M)) : ℝ≥0∞ :=
  ⨅ Γ : {Γ : Set M // IsEnclosingCut M Γ}, area M g Γ.val
end
end CKSGeometricCuts

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
universe u

lemma rawHausdorffArea_lower {X : Type u} (m n : EMetricSpace X) {c : ℝ≥0}
    (hc : 0 < c)
    (h : ∀ x y : X, (c : ℝ≥0∞) * @edist X m.toEDist x y ≤ @edist X n.toEDist x y)
    (s : Set X) :
    (c : ℝ≥0∞)^2 * rawHausdorffArea m s ≤ rawHausdorffArea n s := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hcE : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc0
  have ha : @AntilipschitzWith X X m.toPseudoEMetricSpace n.toPseudoEMetricSpace c⁻¹ id := by
    intro x y
    change @edist X m.toEDist x y ≤ (↑(c⁻¹) : ℝ≥0∞) * @edist X n.toEDist x y
    rw [ENNReal.coe_inv hc0]
    calc
      _ = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * @edist X m.toEDist x y) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel hcE ENNReal.coe_ne_top,one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (h x y)
  have hm := @AntilipschitzWith.le_hausdorffMeasure_image X X m n
    (@borel X m.toUniformSpace.toTopologicalSpace)
    (@BorelSpace.mk X m.toUniformSpace.toTopologicalSpace (@borel X m.toUniformSpace.toTopologicalSpace) rfl)
    (@borel X n.toUniformSpace.toTopologicalSpace)
    (@BorelSpace.mk X n.toUniformSpace.toTopologicalSpace (@borel X n.toUniformSpace.toTopologicalSpace) rfl) id c⁻¹ (2 : ℝ) ha (by norm_num) s
  simp only [Set.image_id] at hm
  change rawHausdorffArea m s ≤ (↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) * rawHausdorffArea n s at hm
  have he : (c : ℝ≥0∞)^2 * (↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = (2 : ℕ) from rfl,ENNReal.rpow_natCast,ENNReal.coe_inv hc0,
      ← mul_pow,ENNReal.mul_inv_cancel hcE ENNReal.coe_ne_top,one_pow]
  calc
    _ ≤ (c : ℝ≥0∞)^2 * ((↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) * rawHausdorffArea n s) :=
      mul_le_mul' le_rfl hm
    _ = _ := by rw [← mul_assoc,he,one_mul]
end
end CKSGeometricCuts

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory CKSReplacementCompleteness
open scoped ContDiff ENNReal NNReal
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H3 M]
  [IsManifold I3 1 M] [T3Space M]

theorem area_lower (g G : Metric I3 (M := M)) {ε : ℝ}
    (hε1 : ε < 1) (hlow : MetricLower I3 g G ε) (Γ : Set M) :
    ENNReal.ofReal (1-ε) * area M g Γ ≤ area M G Γ := by
  let c : ℝ≥0 := ⟨Real.sqrt (1-ε),Real.sqrt_nonneg _⟩
  have hc : 0 < c := Real.sqrt_pos.mpr (sub_pos.mpr hε1)
  have he : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (1-ε)) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)).symm
  have hs : (c : ℝ≥0∞)^2 = ENNReal.ofReal (1-ε) := by
    rw [he,← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,Real.sq_sqrt (le_of_lt (sub_pos.mpr hε1))]
  have hdist : ∀ x y : M, (c : ℝ≥0∞) * @edist M (metricSpace I3 g).toEDist x y ≤
      @edist M (metricSpace I3 G).toEDist x y := by
    intro x y
    rw [he,metricSpace_edist,metricSpace_edist]
    exact metricEDist_lower I3 g G hε1 hlow x y
  have hraw := rawHausdorffArea_lower (metricSpace I3 g) (metricSpace I3 G) hc hdist Γ
  rw [hs] at hraw
  unfold area
  calc
    _ = ENNReal.ofReal (Real.pi/4) * (ENNReal.ofReal (1-ε) * rawHausdorffArea (metricSpace I3 g) Γ) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hraw

theorem geometric_min_area_lower (g G : Metric I3 (M := M)) {ε : ℝ}
    (_hε0 : 0 ≤ ε) (hε1 : ε < 1) (hlow : MetricLower I3 g G ε) :
    ENNReal.ofReal (1-ε) * minEnclosingArea M g ≤ minEnclosingArea M G := by
  unfold minEnclosingArea
  refine le_iInf fun Γ => ?_
  calc
    _ ≤ ENNReal.ofReal (1-ε) * area M g Γ.val := mul_le_mul' le_rfl (iInf_le _ Γ)
    _ ≤ _ := area_lower g G hε1 hlow Γ.val

def identityOuterDomain [IsManifold I3 ∞ M] [ConnectedSpace M]
    (hS : IsCompact (I3.boundary M)) : OuterDomain M where
  Carrier := M
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  inclusion := id
  embedding := IsSmoothEmbedding.id
  closed := by simpa only [range_id] using (isClosed_univ : IsClosed (univ : Set M))
  connected := by simpa only [range_id] using (isConnected_univ : IsConnected (univ : Set M))
  contains_distant_end := ⟨∅,isCompact_empty,by simp⟩
  interior_into := by simp
  compact_boundary := by simpa using hS

omit [IsManifold I3 1 M] [T3Space M] in
theorem boundary_isEnclosingCut [IsManifold I3 1 M] [T3Space M]
    [IsManifold I3 ∞ M] [ConnectedSpace M]
    (hS : IsCompact (I3.boundary M)) : IsEnclosingCut M (I3.boundary M) := by
  refine ⟨identityOuterDomain hS, ?_⟩
  simp only [OuterDomain.cut,identityOuterDomain,Set.image_id]
  rfl
omit [IsManifold I3 1 M] [T3Space M] in
lemma IsEnclosingCut.isCompact [IsManifold I3 1 M] [T3Space M]
    {Γ : Set M} (h : IsEnclosingCut M Γ) : IsCompact Γ := by
  obtain ⟨D,rfl⟩ := h
  exact D.compact_boundary

theorem minEnclosingArea_le_boundary [IsManifold I3 ∞ M] [ConnectedSpace M]
    (hS : IsCompact (I3.boundary M)) (g : Metric I3 (M := M)) :
    minEnclosingArea M g ≤ area M g (I3.boundary M) :=
  iInf_le_of_le ⟨I3.boundary M,boundary_isEnclosingCut hS⟩ le_rfl
end
end CKSGeometricCuts

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_id_isometric CKSMetricGluing.real_continuousAdd
  CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass

theorem covector_smulCommClass {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] :
    letI := CKSLorentz.real_smulCommClass
    SMulCommClass ℝ ℝ (Space →L[ℝ] ℝ) := by
  infer_instance

attribute [local instance] covector_smulCommClass

abbrev SpatialTangentTriv := Trivialization E (π E (fun x : M => TangentSpace I x))
local instance spatialScalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) := ⟨rfl⟩
def spatialBilinearTriv (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    Trivialization SpatialBilinear (π SpatialBilinear (fun x : M =>
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  letI := CKSLorentz.real_smulCommClass
  e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ))
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]

omit [IsManifold I3 ∞ N] [T3Space N] in
theorem boosted_exterior_coordinates [IsManifold I3 ∞ N] [T3Space N]
    {e : ℝ} {p : E} (he : ‖p‖ < e)
    (f : N → E) (finv : E → N) {U : Set N} {S : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (T₀ : ℝ) :
    let H := hyperbolicHomeomorph e p he
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ T : ℝ, 0 < T ∧ T₀ ≤ T ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
      ∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r} := by
  classical
  dsimp only
  let H := hyperbolicHomeomorph e p he
  let f' := H.symm ∘ f
  let inv' := finv ∘ H
  obtain ⟨T,hT,hTT₀,hfar,hVo,hVc⟩ := boosted_end_proper H f hU hf.continuousOn hclosed T₀
  let V : Set N := {x | x ∈ U ∧ T < ‖f' x‖}
  have hHs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H :=
    (hyperbolicMap_smooth e (mass e p) p).contMDiff
  have hHis : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H.symm :=
    (hyperbolicMap_smooth e (mass e p) (-p)).contMDiff
  have hf' : ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V :=
    (hHis.comp_contMDiffOn hf).mono (fun x hx => hx.1)
  have hi' : ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} :=
    hi.comp hHs.contMDiffOn (fun y hy => lt_trans (by linarith : S < S+1) (hfar y hy))
  refine ⟨T,hT,hTT₀,hVo,hf',hi',?_,?_,hVc,?_⟩
  · intro x hx
    change finv (H (H.symm (f x))) = x
    rw [H.apply_symm_apply]
    exact hleft x hx.1
  · intro y hy
    have hyr := hright (H y) (lt_trans (by linarith : S < S+1) (hfar y hy))
    have hfy : f' (inv' y) = y := by
      change H.symm (f (finv (H y))) = y
      rw [hyr.2,H.symm_apply_apply]
    exact ⟨⟨hyr.1,by change T < ‖f' (inv' y)‖; rw [hfy]; exact hy⟩,hfy⟩
  · intro r hr
    obtain ⟨B,hB,hBS,hBr⟩ := homeomorph_maps_far_tail H.symm r (S+1)
    have hc := hcompact B (lt_of_lt_of_le (by linarith : S < S+1) hBS)
    have hopen : IsOpen {x : N | x ∈ V ∧ r < ‖f' x‖} :=
      hf'.continuousOn.norm.isOpen_inter_preimage hVo isOpen_Ioi
    have hcl : IsClosed {x : N | x ∉ V ∨ ‖f' x‖ ≤ r} := by
      convert hopen.isClosed_compl using 1
      ext x
      simp only [mem_compl_iff,mem_ofPred_eq,not_and_or,not_lt]
    exact hc.of_isClosed_subset hcl (by
      intro x hx
      by_cases hxU : x ∈ U
      · right
        by_contra hxb
        have hfar' : r < ‖f' x‖ := hBr (f x) (lt_of_not_ge hxb)
        have hxV : x ∈ V := ⟨hxU,hr.trans_lt hfar'⟩
        exact hx.elim (fun h => h hxV) (fun h => (not_lt_of_ge h) hfar')
      · exact Or.inl hxU)
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] spatialScalarAtlas real_id_isometric CKSMetricGluing.real_continuousAdd
  CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass
  covector_smulCommClass
local instance bilNorm : NormedAddCommGroup SpatialBilinear :=
  letI := CKSLorentz.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance bilSpace : NormedSpace ℝ SpatialBilinear :=
  letI := CKSLorentz.real_smulCommClass
  letI := covector_smulCommClass (Space := E)
  ContinuousLinearMap.toNormedSpace
instance spatialBilinearTriv_atlas (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    MemTrivializationAtlas (spatialBilinearTriv I e) := by unfold spatialBilinearTriv; infer_instance
@[simp] lemma spatialBilinearTriv_baseSet (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    (spatialBilinearTriv I e).baseSet = e.baseSet := by simp [spatialBilinearTriv]
lemma spatialBilinearTriv_pair (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((spatialBilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
  let := CKSLorentz.real_smulCommClass
  unfold spatialBilinearTriv
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ))
    (show x ∈ (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ)).baseSet by simpa using hx)]
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (Trivial.trivialization M ℝ) (show x ∈ (Trivial.trivialization M ℝ).baseSet from mem_univ x)]
  rfl
lemma mfderiv_gauge_smooth {f : M → E} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, E) ∞ f x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun y => ((NormedSpace.fromTangentSpace (f y)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, E) f y)).comp
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  have h := hf.mfderiv_const (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  convert! h using 1
  funext y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space, NormedSpace.fromTangentSpace]
  rfl

omit [IsManifold I ∞ M] in
lemma bilinearComp_smoothAt [IsManifold I ∞ M]
    {B : M → SpatialBilinear} {A : M → E →L[ℝ] E} {x : M}
    (hB : ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ B x)
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  have flipSmooth : ContDiff ℝ ∞ (fun B : SpatialBilinear => B.flip) :=
    by
      let L : SpatialBilinear →L[ℝ] SpatialBilinear := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      exact L.contDiff
  exact flipSmooth.comp_contMDiffAt
    ((flipSmooth.comp_contMDiffAt (hB.clm_comp hA)).clm_comp hA)
lemma endInner_smoothAt {f : M → E} {A : SpatialTensor} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x)
    (hA : ContDiffAt ℝ ∞ A (f x)) :
    ContMDiffAt I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞
      (innerSection I (endInner I f A)) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  apply ((spatialBilinearTriv I e).contMDiffAt_section_iff (IB := I) (n := ∞)
    (F := SpatialBilinear) (s := endInner I f A)
    (show x ∈ (spatialBilinearTriv I e).baseSet by simpa using hx)).mpr
  have hB := hA.contMDiffAt.comp x hf
  apply (bilinearComp_smoothAt hB (mfderiv_gauge_smooth hf)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  ext v w
  rw [spatialBilinearTriv_pair e hy]
  rfl
lemma positive_bilinear_bounded (B : SpatialBilinear) (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : E | B v v < 1} := by
  have hc : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
  have hp : 0 < B a a := hB a ha0
  have hlow : ∀ v : E, B a a * ‖v‖ ^ 2 ≤ B v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E) 1 by
      simpa [Metric.mem_sphere] using hy)
    have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      field_simp
    change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
    rw [he] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_iff_subset_ball (0 : E)).mpr
  refine ⟨1 + (B a a)⁻¹, ?_⟩
  intro v hv
  change dist v 0 < 1 + (B a a)⁻¹
  rw [dist_zero_right]
  have hbv : B v v < 1 := hv
  have hl := hlow v
  have hinv : 0 < (B a a)⁻¹ := inv_pos.mpr hp
  have he : B a a * (B a a)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  by_contra hh
  have hn : 1 + (B a a)⁻¹ ≤ ‖v‖ := le_of_not_gt hh
  have hn1 : 1 ≤ ‖v‖ := by linarith
  have hn2 : ‖v‖ ≤ ‖v‖^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn hp.le
  have hmul2 := mul_le_mul_of_nonneg_left hn2 hp.le
  nlinarith
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] Classical.propDecidable
lemma end_extend_smooth (old : InnerField I (M := M))
    (hOld : ContMDiff I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I old))
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A G : SpatialTensor)
    (hsource : ∀ x ∈ U, old x = endInner I f A x)
    (hR : T < R)
    (hG : ContDiffOn ℝ ∞ G {x | T < ‖x‖})
    (hold : ∀ x, ‖x‖ ≤ R → G x = A x) :
    ContMDiff I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞
      (innerSection I (fun x => if x ∈ U then endInner I f G x else old x)) := by
  intro x
  by_cases hx : x ∈ U
  · have hGat := (hG (f x) (htail x hx)).contDiffAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (htail x hx))
    apply (endInner_smoothAt ((hf x hx).contMDiffAt (hU.mem_nhds hx)) hGat).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [innerSection,ite_eq_left hy]
  · let c := (T+R)/2
    have hcT : T < c := by dsimp [c]; linarith
    have hcR : c < R := by dsimp [c]; linarith
    have hx' : x ∈ {x : M | x ∈ U ∧ c ≤ ‖f x‖}ᶜ := by simp [hx]
    apply (hOld x).congr_of_eventuallyEq
    filter_upwards [(hclosed c hcT).isOpen_compl.mem_nhds hx'] with y hy
    by_cases hyU : y ∈ U
    · have hyR : ‖f y‖ ≤ R := by
        have : ¬ c ≤ ‖f y‖ := fun hc => hy ⟨hyU,hc⟩
        exact (lt_of_not_ge this).le.trans hcR.le
      simp only [innerSection,ite_eq_left hyU,hsource y hyU]
      congr 1
      unfold endInner
      rw [hold (f y) hyR]
    · simp only [innerSection,ite_eq_right hyU]
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M] [T3Space M]

theorem extend_actual_end (g : SmoothMetric I3 (M := M))
    (K : InnerField I3 (M := M))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R ε : ℝ}
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A B G k : SpatialTensor)
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f A x ∧ K x = endInner I3 f B x)
    (hR : T < R) (hε : 0 ≤ ε)
    (hG : ContDiffOn ℝ ∞ G {x | T < ‖x‖})
    (hk : ContDiffOn ℝ ∞ k {x | T < ‖x‖})
    (hGsym : ∀ x, T < ‖x‖ → ∀ v w, G x v w = G x w v)
    (hksym : ∀ x, T < ‖x‖ → ∀ v w, k x v w = k x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < G x v v)
    (hold : ∀ x, ‖x‖ ≤ R → G x = A x ∧ k x = B x)
    (hlower : ∀ x, T < ‖x‖ → ∀ v : E, (1-ε)*A x v v ≤ G x v v) :
    ∃ (g' : SmoothMetric I3 (M := M)) (K' : InnerField I3 (M := M)),
      ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
      (∀ x v w, K' x v w = K' x w v) ∧
      (∀ x ∈ U, g'.inner x = endInner I3 f G x ∧ K' x = endInner I3 f k x) ∧
      (∀ x, (x ∉ U ∨ ‖f x‖ ≤ R) → g'.inner x = g.inner x ∧ K' x = K x) ∧
      CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric ε ∧
      (ε < 1 → CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric →
        CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric) ∧
      (ε < 1 → ENNReal.ofReal (1-ε)*minEnclosingArea M g.toContinuousRiemannianMetric ≤
        minEnclosingArea M g'.toContinuousRiemannianMetric) := by
  classical
  let Q : InnerField I3 (M := M) := fun x => if x ∈ U then endInner I3 f G x else g.inner x
  let L : InnerField I3 (M := M) := fun x => if x ∈ U then endInner I3 f k x else K x
  have hQs : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 Q) :=
    end_extend_smooth g.inner g.contMDiff f hU hf htail hclosed A G
      (fun x hx => (hsource x hx).1) hR hG (fun x hx => (hold x hx).1)
  have hLs : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 L) :=
    end_extend_smooth K hK f hU hf htail hclosed B k
      (fun x hx => (hsource x hx).2) hR hk (fun x hx => (hold x hx).2)
  have hQsym : ∀ x v w, Q x v w = Q x w v := by
    intro x v w
    by_cases hx : x ∈ U
    · change (if x ∈ U then endInner I3 f G x else g.inner x) v w =
        (if x ∈ U then endInner I3 f G x else g.inner x) w v
      rw [ite_eq_left hx]
      exact hGsym (f x) (htail x hx) _ _
    · simpa only [Q,ite_eq_right hx] using g.symm x v w
  have hQpos : ∀ x (v : TangentSpace I3 x), v ≠ 0 → 0 < Q x v v := by
    intro x v hv
    by_cases hx : x ∈ U
    · let df := (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv I3 𝓘(ℝ,E) f x)
      have hvd : df v ≠ 0 := by
        intro hz
        have hp := g.pos x v hv
        rw [(hsource x hx).1] at hp
        change 0 < A (f x) (df v) (df v) at hp
        simp only [hz,map_zero,lt_self_iff_false] at hp
      change 0 < (if x ∈ U then endInner I3 f G x else g.inner x) v v
      rw [ite_eq_left hx]
      exact hpos (f x) (htail x hx) (df v) hvd
    · simpa only [Q,ite_eq_right hx] using g.pos x v hv
  let g' : SmoothMetric I3 (M := M) := {
    inner := Q
    symm := hQsym
    pos := hQpos
    isVonNBounded := fun x => positive_bilinear_bounded (Q x) (hQpos x)
    contMDiff := hQs }
  have hlow : CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric
      g'.toContinuousRiemannianMetric ε := by
    intro x v
    change (1-ε)*g.inner x v v ≤ Q x v v
    by_cases hx : x ∈ U
    · rw [(hsource x hx).1]
      change (1-ε)*endInner I3 f A x v v ≤
        (if x ∈ U then endInner I3 f G x else g.inner x) v v
      rw [ite_eq_left hx]
      exact hlower (f x) (htail x hx) _
    · simp only [Q,ite_eq_right hx]
      have hn : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos x v hv).le
      nlinarith
  refine ⟨g',L,hLs,?_,?_,?_,hlow,?_,?_⟩
  · intro x v w
    by_cases hx : x ∈ U
    · change (if x ∈ U then endInner I3 f k x else K x) v w =
        (if x ∈ U then endInner I3 f k x else K x) w v
      rw [ite_eq_left hx]
      exact hksym (f x) (htail x hx) _ _
    · simpa only [L,ite_eq_right hx] using hKsym x v w
  · intro x hx
    exact ⟨by simp [g',Q,hx],by simp [L,hx]⟩
  · intro x hx
    by_cases hxU : x ∈ U
    · have hxR : ‖f x‖ ≤ R := hx.resolve_left (not_not_intro hxU)
      have hGA : endInner I3 f G x = endInner I3 f A x := by
        unfold endInner
        rw [(hold (f x) hxR).1]
      have hkB : endInner I3 f k x = endInner I3 f B x := by
        unfold endInner
        rw [(hold (f x) hxR).2]
      simpa only [g',Q,L,ite_eq_left hxU,hGA,hkB] using
        ⟨(hsource x hxU).1.symm,(hsource x hxU).2.symm⟩
    · simp [g',Q,L,hxU]
  · intro hε1 hg
    exact CKSReplacementCompleteness.complete_of_metricLower I3
      g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric hε hε1 hg hlow
  · intro hε1
    exact geometric_min_area_lower g.toContinuousRiemannianMetric
      g'.toContinuousRiemannianMetric hε hε1 hlow
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] CKSLorentz.hsgNorm CKSLorentz.hsgSpace

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma endInner_fullRank (g : SmoothMetric I (M := M)) (f : M → E)
    (A : SpatialTensor) {x : M} (heq : g.inner x = endInner I f A x) :
    Function.Bijective (mfderiv I 𝓘(ℝ,E) f x) := by
  let : FiniteDimensional ℝ (TangentSpace I x) := by exact (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (mfderiv I 𝓘(ℝ,E) f x) := by
    intro v w hvw
    by_contra hne
    have hp := g.pos x (v-w) (sub_ne_zero.mpr hne)
    rw [heq] at hp
    have hz : (mfderiv I 𝓘(ℝ,E) f x) (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    change 0 < A (f x) ((mfderiv I 𝓘(ℝ,E) f x) (v-w))
      ((mfderiv I 𝓘(ℝ,E) f x) (v-w)) at hp
    rw [hz] at hp
    have ha : A (f x) (0:E) (0:E) = 0 := by simp
    exact (lt_irrefl 0) (ha ▸ hp)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
omit [IsManifold I ∞ M] in
lemma PhysicalDECAt.congr_nhds [IsManifold I ∞ M]
    {g K g' K' : InnerField I (M := M)} {x : M}
    (h : PhysicalDECAt I g K x)
    (heq : {y : M | g' y = g y ∧ K' y = K y} ∈ 𝓝 x) :
    PhysicalDECAt I g' K' x := by
  obtain ⟨U,f,A,B,hU,hx,hf,hd,hs,hp,he,hDEC⟩ := h
  obtain ⟨V,hV,hVo,hVx⟩ := mem_nhds_iff.mp heq
  refine ⟨U∩V,f,A,B,hU.inter hVo,⟨hx,hVx⟩,hf.mono inter_subset_left,
    fun y hy => hd y hy.1,fun y hy => hs y hy.1,fun y hy => hp y hy.1,?_,hDEC⟩
  intro y hy
  exact ⟨(hV hy.2).1.trans (he y hy.1).1,(hV hy.2).2.trans (he y hy.1).2⟩
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem extended_manifold_DEC (g g' : SmoothMetric I (M := M))
    (K K' : InnerField I (M := M)) (hDEC : PhysicalDEC I g.inner K)
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R : ℝ} (hR : T < R)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A {x | T < ‖x‖})
    (hBs : ContDiffOn ℝ ∞ B {x | T < ‖x‖})
    (hA : ∀ x, T < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, T < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < A x v v)
    (hnew : ∀ x, T < ‖x‖ → spatialDEC A B x)
    (hend : ∀ x ∈ U, g'.inner x = endInner I f A x ∧ K' x = endInner I f B x)
    (hold : ∀ x, (x ∉ U ∨ ‖f x‖ ≤ R) → g'.inner x = g.inner x ∧ K' x = K x) :
    PhysicalDEC I g'.inner K' := by
  intro x
  by_cases hx : x ∈ U
  · refine ⟨U,f,A,B,hU,hx,hf,?_,?_,?_,hend,hnew (f x) (htail x hx)⟩
    · intro y hy
      exact endInner_fullRank g' f A (hend y hy).1
    · intro y hy
      have ho := (isOpen_lt continuous_const continuous_norm).mem_nhds (htail y hy)
      exact ⟨(hAs (f y) (htail y hy)).contDiffAt ho,(hBs (f y) (htail y hy)).contDiffAt ho⟩
    · intro y hy
      exact ⟨hA (f y) (htail y hy),hpos (f y) (htail y hy),hB (f y) (htail y hy)⟩
  · apply (hDEC x).congr_nhds
    let c := (T+R)/2
    have hcT : T < c := by dsimp [c]; linarith
    have hcR : c < R := by dsimp [c]; linarith
    have hx' : x ∈ {x : M | x ∈ U ∧ c ≤ ‖f x‖}ᶜ := by simp [hx]
    filter_upwards [(hclosed c hcT).isOpen_compl.mem_nhds hx'] with y hy
    apply hold
    by_cases hyU : y ∈ U
    · right
      have hh : ¬ c ≤ ‖f y‖ := fun hz => hy ⟨hyU,hz⟩
      exact (lt_of_not_ge hh).le.trans hcR.le
    · exact Or.inl hyU
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
omit [IsManifold I ∞ M] in
lemma endInner_comp [IsManifold I ∞ M] {F : E → E} {f : M → E}
    (A : SpatialTensor) {x : M}
    (hF : ContDiffAt ℝ ∞ F (f x)) (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I (F ∘ f) A x = endInner I f (spatialTensorPullback F A) x := by
  have hc := mfderiv_comp x (hF.contMDiffAt.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  ext v w
  change A (F (f x)) ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) v)
      ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) w) =
    A (F (f x)) ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) v))
      ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) w))
  rw [hc]
  rfl
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem endInner_balanced {e : ℝ} {p : E} (he : ‖p‖ < e)
    (f : M → E) (A : SpatialTensor) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I ((hyperbolicHomeomorph e p he).symm ∘ f)
      (sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)) x =
      endInner I f (sourceSpatial A) x := by
  rw [sourceSpatial_boost he]
  let h := hyperbolicHomeomorph e p he
  have hi : ContDiff ℝ ∞ h.symm := hyperbolicMap_smooth e (mass e p) (-p)
  have hs : ContDiff ℝ ∞ h := hyperbolicMap_smooth e (mass e p) p
  have hf' : ContMDiffAt I 𝓘(ℝ,E) ∞ (h.symm ∘ f) x := hi.contDiffAt.contMDiffAt.comp x hf
  have ht := endInner_comp (I := I) (F := h) (f := h.symm ∘ f)
    (sourceSpatial A) hs.contDiffAt hf'
  have heq : h ∘ (h.symm ∘ f) = f := by funext y; exact h.apply_symm_apply (f y)
  rw [heq] at ht
  exact ht.symm
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

theorem compact_side_eventually (f : M → E) {U : Set M} {T : ℝ}
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    {C : Set M} (hC : IsCompact C) :
    ∃ R : ℝ, T < R ∧ ∀ r ≥ R, ∀ x ∈ C, x ∉ U ∨ ‖f x‖ ≤ r := by
  classical
  let V : ℕ → Set M := fun n => {x : M | x ∈ U ∧ T+(n:ℝ)+1 ≤ ‖f x‖}ᶜ
  have hVo : ∀ n, IsOpen (V n) := by
    intro n
    exact (hclosed _ (by have : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)).isOpen_compl
  have hcover : C ⊆ ⋃ n, V n := by
    intro x hx
    obtain ⟨n,hn⟩ := exists_nat_gt (‖f x‖-T)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    intro hy
    have hh : T+(n:ℝ)+1 ≤ ‖f x‖ := hy.2
    linarith
  obtain ⟨q,hq⟩ := hC.elim_finite_subcover V hVo hcover
  refine ⟨T+(q.sup id:ℕ)+1,?_,?_⟩
  · have : 0 ≤ ((q.sup id:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  · intro r hr x hx
    by_cases hxU : x ∈ U
    · right
      obtain ⟨n,hn⟩ := mem_iUnion.mp (hq hx)
      obtain ⟨hnq,hm⟩ := mem_iUnion.mp hn
      have hnle : n ≤ q.sup id := Finset.le_sup (f := id) hnq
      have hnr : (n:ℝ) ≤ ((q.sup id:ℕ):ℝ) := by exact_mod_cast hnle
      have hlt : ‖f x‖ < T+(n:ℝ)+1 := by
        exact lt_of_not_ge (fun h => hm ⟨hxU,h⟩)
      linarith
    · exact Or.inl hxU
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter MeasureTheory CKSLorentz CKSMetricGluing CKSGeometricCuts
open CKSSphericalHarmonics CKSADM CKSBending
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]

theorem original_CKS_replacement_coordinate_package
    {M : CKSLorentz.Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : CKSLorentz.Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hgDEC : PhysicalDEC I3 g.inner K)
    (hgcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (f : N → E) {U : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (finv : E → N)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f (sourceSpatial A) x ∧
      K x = endInner I3 f (sourceSpatial B) x)
    {C : Set N} (hC : IsCompact C) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let H := hyperbolicHomeomorph e p ht
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r}) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (g' : SmoothMetric I3 (M := N)) (K' : InnerField I3 (M := N)),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
          (∀ x v w, K' x v w = K' x w v) ∧
          PhysicalDEC I3 g'.inner K' ∧
          CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric ∧
          (∀ x ∈ C, g'.inner x = g.inner x ∧ K' x = K x) ∧
          (∀ x, x ∉ V ∨ ‖f' x‖ ≤ R → g'.inner x = g.inner x ∧ K' x = K x) ∧
          CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric (ε R) ∧
          ENNReal.ofReal (1-ε R)*minEnclosingArea N g.toContinuousRiemannianMetric ≤
            minEnclosingArea N g'.toContinuousRiemannianMetric ∧
          (∀ x, x ∈ U ∧ T < ‖f' x‖ →
            g'.inner x = endInner I3 f' (G R) x ∧ K' x = endInner I3 f' (k R) x) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
          (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
          Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
          Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
          0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
          (∀ s : ℝ, T < s →
            IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
            IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
              (CKSAngularGeometry.physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
              (CKSAngularGeometry.physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
              (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
          ∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0 := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let H := hyperbolicHomeomorph e p ht
  let f' := H.symm ∘ f
  let A' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
  let B' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)
  obtain ⟨T₀,Q,ε,G,k,hT₀,hTQ,hQ,hε,hfar,hend⟩ :=
    original_CKS_end_integrable_replacement hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  obtain ⟨T,hT,hT₀T,hVo,hfsV,hiV,hleftV,hrightV,hVclosed,hVcompact⟩ :=
    boosted_exterior_coordinates ht f finv hU hf hi hleft hright hclosed hcompact T₀
  let V : Set N := {x | x ∈ U ∧ T < ‖f' x‖}
  have hVopen : IsOpen V := hVo
  have hVc : ∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖} := hVclosed
  have hfs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H.symm :=
    (hyperbolicMap_smooth e (mass e p) (-p)).contMDiff
  have hf' : ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V :=
    (hfs.comp_contMDiffOn hf).mono (fun x hx => hx.1)
  have hVtail : ∀ x ∈ V, T < ‖f' x‖ := fun x hx => hx.2
  have hsame : ∀ x ∈ V, g.inner x = endInner I3 f' A' x ∧ K x = endInner I3 f' B' x := by
    intro x hx
    have hsx := hf.contMDiffAt (hU.mem_nhds hx.1)
    exact ⟨(hsource x hx.1).1.trans (endInner_balanced ht f A hsx).symm,
      (hsource x hx.1).2.trans (endInner_balanced ht f B hsx).symm⟩
  obtain ⟨D,hD,hDC⟩ := compact_side_eventually f' hVc hC
  let R₀ := max Q (max (T+1) D)
  have hQR : Q ≤ R₀ := le_max_left _ _
  have hTR : T < R₀ := lt_of_lt_of_le (by linarith : T < T+1)
    ((le_max_left _ _).trans (le_max_right _ _))
  have hDR : D ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,R₀,ε,G,k,hTR,hQ.trans hQR,hε,hVopen,hfsV,hiV,hleftV,hrightV,hVcompact,?_⟩
  intro R hR
  obtain ⟨heps,hGs,hks,hgeom,holdR,hzero,hAF,hE,hP,hpad0,hpad1,hint,hmom⟩ := hend R (hQR.trans hR)
  have hGs' := hGs.mono (fun x hx => hT₀T.trans_lt hx)
  have hks' := hks.mono (fun x hx => hT₀T.trans_lt hx)
  have hgeom' (x : E) (hx : T < ‖x‖) := hgeom x (hT₀T.trans_lt hx)
  obtain ⟨g',K',hK',hKsym',hnew,hold',hlower,hcomplete,harea⟩ :=
    extend_actual_end g K hK hKsym f' hVopen hf' hVtail hVc A' B' (G R) (k R)
      hsame (hTR.trans_le hR) heps.1 hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      holdR (fun x hx => (hgeom' x hx).2.2.2.2)
  have hDECall : PhysicalDEC I3 g'.inner K' :=
    extended_manifold_DEC g g' K K' hgDEC f' hVopen (hTR.trans_le hR) hf' hVtail hVc
      (G R) (k R) hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      (fun x hx => (hgeom' x hx).2.2.2.1) hnew hold'
  refine ⟨heps,g',K',hK',hKsym',hDECall,hcomplete heps.2 hgcomplete,?_,
    hold',hlower,harea heps.2,hnew,hzero,hAF,hE,hP,hpad0,hpad1,
    (fun s hs => hint s (hT₀T.trans_lt hs)),hmom⟩
  intro x hx
  exact hold' x (hDC R (hDR.trans hR) x hx)
end
end CKSSpatialManifold

end

end OAI
