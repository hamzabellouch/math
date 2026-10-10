import Mathlib
import OAI.MathematicalPhysics.BFSS.ProfileExtraction

namespace OAI

/-! Closed charge graphs, continuous profiles and extraction from graph closures. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)

lemma deformedCoreCharge_add (h m : ℝ) (α : SpinIndex) (f g : SmoothCore N) :
    M.deformedCoreCharge h m α (f+g) =
      M.deformedCoreCharge h m α f + M.deformedCoreCharge h m α g := by
  unfold deformedCoreCharge
  simp only [map_add]
  abel

lemma deformedCoreCharge_smul (h m : ℝ) (α : SpinIndex) (c : ℂ) (f : SmoothCore N) :
    M.deformedCoreCharge h m α (c • f) = c • M.deformedCoreCharge h m α f := by
  apply DFunLike.ext
  intro x
  simp only [deformedCoreCharge_apply, IsSMulApply.smul_apply, smul_add, map_smul]
  congr 1
  rw [smul_comm]
  congr 1
  simp only [BFSSKinetic.kineticDerivative_apply,
    _root_.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change M.kineticComplexSymbol α p ((coordinateDerivative p.1 p.2 (c • f)) x) =
    c • M.kineticComplexSymbol α p ((coordinateDerivative p.1 p.2 f) x)
  rw [map_smul]
  change M.kineticComplexSymbol α p (c • (coordinateDerivative p.1 p.2 f) x) = _
  exact map_smul _ _ _

def deformedChargeMap (h m : ℝ) (α : SpinIndex) : SmoothCore N →ₗ[ℂ] SmoothCore N where
  toFun := M.deformedCoreCharge h m α
  map_add' := M.deformedCoreCharge_add h m α
  map_smul' := M.deformedCoreCharge_smul h m α

lemma coreInner_re_eq_mixed (f g : SmoothCore N) :
    (inner ℂ (coreToL2 f) (coreToL2 g)).re =
      inner ℝ (MixedEnergy.toL2 f) (MixedEnergy.toL2 g) := by
  rw [coreToL2_inner, MixedEnergy.toL2_inner]
  change RCLike.re (∫ x, inner ℂ (f x) (g x)) = _
  rw [← integral_re (coreInner_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [PiLp.inner_apply, map_sum, RCLike.re_to_complex, real_inner_eq_re_inner ℂ]

lemma deformedCoreCharge_re_symmetric (h m : ℝ) (α : SpinIndex) (f g : SmoothCore N) :
    (inner ℂ (coreToL2 (M.deformedCoreCharge h m α f)) (coreToL2 g)).re =
      (inner ℂ (coreToL2 f) (coreToL2 (M.deformedCoreCharge h m α g))).re := by
  rw [coreInner_re_eq_mixed, coreInner_re_eq_mixed]
  have hk := MixedEnergy.firstOrder_symmetric (M.kineticSkewSymbol α)
    (M.kineticSkewSymbol_skew α) f g
  have hv := MixedEnergy.field_symmetric (M.deformedRealField h m α)
    (M.deformedRealField_contDiff h m α) (M.deformedRealField_selfAdjoint h m α) f g
  simpa only [deformedCoreCharge, map_add, inner_add_left, inner_add_right] using
    congrArg₂ (· + ·) hk hv

theorem deformedChargeMap_symmetric (h m : ℝ) (α : SpinIndex) :
    CoreSymmetric (M.deformedChargeMap h m α) := by
  intro f g
  apply Complex.ext
  · exact (M.deformedCoreCharge_re_symmetric h m α f g)
  · have hi := M.deformedCoreCharge_re_symmetric h m α f (Complex.I • g)
    rw [M.deformedCoreCharge_smul] at hi
    simp only [map_smul, inner_smul_right, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub] at hi
    exact neg_injective hi

def deformedChargeVector (h m : ℝ) : SmoothCore N →ₗ[ℂ] (SpinIndex → FullL2 N) :=
  LinearMap.pi (fun α => coreToL2.comp (M.deformedChargeMap h m α))

def deformedCoreGraph (h m : ℝ) : Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  LinearMap.range (coreToL2.prod (M.deformedChargeVector h m))

def deformedClosedGraph (h m : ℝ) : Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  (M.deformedCoreGraph h m).topologicalClosure

lemma deformedClosedGraph_pairing (h m : ℝ)
    {p : FullL2 N × (SpinIndex → FullL2 N)} (hp : p ∈ M.deformedClosedGraph h m)
    (α : SpinIndex) (f : SmoothCore N) :
    inner ℂ (coreToL2 (M.deformedCoreCharge h m α f)) p.1 =
      inner ℂ (coreToL2 f) (p.2 α) := by
  let S : Set (FullL2 N × (SpinIndex → FullL2 N)) :=
    {p | inner ℂ (coreToL2 (M.deformedCoreCharge h m α f)) p.1 =
      inner ℂ (coreToL2 f) (p.2 α)}
  have hc : IsClosed S := isClosed_eq (continuous_const.inner continuous_fst)
    (continuous_const.inner ((continuous_apply α).comp continuous_snd))
  have hs : (M.deformedCoreGraph h m : Set _) ⊆ S := by
    rintro p ⟨g,rfl⟩
    exact M.deformedChargeMap_symmetric h m α f g
  exact closure_minimal hs hc hp

theorem deformedClosedGraph_vertical (h m : ℝ) {y : SpinIndex → FullL2 N}
    (hy : ((0 : FullL2 N),y) ∈ M.deformedClosedGraph h m) : y = 0 := by
  funext α
  apply coreToL2_dense.eq_zero_of_inner_right (𝕜 := ℂ)
  intro f
  have he := M.deformedClosedGraph_pairing h m hy α f
  simpa only [inner_zero_right] using he.symm

end
end BFSSQuantum.AlgebraData
namespace BFSSRellich
lemma normSquare_distance_le {X : Type*} [NormedAddCommGroup X] (x y : X) :
    dist (‖x‖^2) (‖y‖^2) ≤ dist x y * (‖x‖+‖y‖) := by
  rw [Real.dist_eq]
  calc |‖x‖^2-‖y‖^2| = |‖x‖-‖y‖| *(‖x‖+‖y‖) := by
         rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),mul_comm]
       _ ≤ dist x y * (‖x‖+‖y‖) := mul_le_mul_of_nonneg_right
         (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)
         (add_nonneg (norm_nonneg _) (norm_nonneg _))
end BFSSRellich
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

def coreNormClosure : Submodule ℂ (FullL2 N) :=
  (LinearMap.range (coreToL2.comp G.invariantCore.subtype)).topologicalClosure

def coreNormEmbedding : G.invariantCore →ₗ[ℂ] G.coreNormClosure :=
  (coreToL2.comp G.invariantCore.subtype).codRestrict G.coreNormClosure (fun f =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ f))

lemma coreNormEmbedding_dense : DenseRange G.coreNormEmbedding := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y,⟨f,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp x.prop ε hε
  exact ⟨G.coreNormEmbedding f,mem_range_self f,hy⟩

lemma coreNormEmbedding_norm (f : G.invariantCore) :
    ‖G.coreNormEmbedding f‖ = ‖coreToL2 f.val‖ := rfl

namespace MeasuredNormalPatch
variable {G} {q : Boson N} (P : G.MeasuredNormalPatch q)

lemma profile_ae (h : ℝ) (f : G.invariantCore) :
    P.profile h f =ᵐ[volume] M.normalMeasuredCoordinates q h P.density P.cutoff f.val :=
  BFSSRellich.compactLp_ae _ _ _

lemma profile_add (h : ℝ) (f g : G.invariantCore) :
    P.profile h (f+g) = P.profile h f + P.profile h g := by
  apply Lp.ext
  filter_upwards [P.profile_ae h (f+g),P.profile_ae h f,P.profile_ae h g,
    Lp.coeFn_add (P.profile h f) (P.profile h g)] with x hfg hf hg ha
  rw [ha,Pi.add_apply,hfg,hf,hg]
  simp only [AlgebraData.normalMeasuredCoordinates,AlgebraData.normalCoordinateField,
    AlgebraData.normalCoreField,Function.comp_apply,Submodule.coe_add,IsAddApply.add_apply,smul_add]

lemma profile_smul (h : ℝ) (c : ℂ) (f : G.invariantCore) :
    P.profile h (c • f) = c • P.profile h f := by
  apply Lp.ext
  filter_upwards [P.profile_ae h (c • f),P.profile_ae h f,
    Lp.coeFn_smul c (P.profile h f)] with x hcf hf hs
  rw [hs,Pi.smul_apply,hcf,hf]
  simp only [AlgebraData.normalMeasuredCoordinates,AlgebraData.normalCoordinateField,
    AlgebraData.normalCoreField,Function.comp_apply,Submodule.coe_smul,IsSMulApply.smul_apply]
  rw [smul_comm c,smul_comm c]

def profileLinear (h : ℝ) : G.invariantCore →ₗ[ℂ]
    Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) where
  toFun := P.profile h
  map_add' := P.profile_add h
  map_smul' := P.profile_smul h

lemma profile_norm_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (f : G.invariantCore) :
    ‖P.profile h f‖ ≤ ‖coreToL2 f.val‖ := by
  have he := P.norm_le h hh h1 f
  rw [←P.profile_norm_square] at he
  nlinarith [norm_nonneg (P.profile h f),norm_nonneg (coreToL2 f.val)]

def closedProfile (h : ℝ) : G.coreNormClosure →L[ℂ]
    Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) :=
  (P.profileLinear h).extendOfNorm G.coreNormEmbedding

lemma closedProfile_core {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (f : G.invariantCore) :
    P.closedProfile h (G.coreNormEmbedding f) = P.profile h f := by
  unfold closedProfile
  apply LinearMap.extendOfNorm_eq G.coreNormEmbedding_dense
  refine ⟨1,fun x => ?_⟩
  rw [one_mul,G.coreNormEmbedding_norm]
  exact P.profile_norm_le hh h1 x

lemma closedProfile_norm_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (x : G.coreNormClosure) :
    ‖P.closedProfile h x‖ ≤ ‖x‖ := by
  unfold closedProfile
  have hf : ∀ f, ‖(P.profileLinear h) f‖ ≤ 1 * ‖G.coreNormEmbedding f‖ := by
    intro f
    rw [one_mul,G.coreNormEmbedding_norm]
    exact P.profile_norm_le hh h1 f
  simpa only [one_mul] using (P.profileLinear h).norm_extendOfNorm_apply_le
    G.coreNormEmbedding_dense 1 hf x

lemma closedProfile_dist_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (x y : G.coreNormClosure) :
    dist (P.closedProfile h x) (P.closedProfile h y) ≤ dist x y := by
  have hs := (P.closedProfile h).map_sub x y
  calc dist (P.closedProfile h x) (P.closedProfile h y) = ‖P.closedProfile h (x-y)‖ := by
         exact (dist_eq_norm _ _).trans (congrArg norm hs.symm)
       _ ≤ ‖x-y‖ := P.closedProfile_norm_le hh h1 (x-y)
       _ = dist x y := (dist_eq_norm x y).symm
lemma closedProfile_core_dist_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1)
    (f : G.invariantCore) (x : G.coreNormClosure) :
    dist (P.profile h f) (P.closedProfile h x) ≤ dist (coreToL2 f.val) (x : FullL2 N) := by
  calc dist (P.profile h f) (P.closedProfile h x) =
      dist (P.closedProfile h (G.coreNormEmbedding f)) (P.closedProfile h x) :=
        congrArg (fun z => dist z (P.closedProfile h x)) (P.closedProfile_core hh h1 f).symm
       _ ≤ dist (G.coreNormEmbedding f) x := P.closedProfile_dist_le hh h1 _ _
       _ = dist (coreToL2 f.val) (x : FullL2 N) := rfl
end MeasuredNormalPatch
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] coreToL2

def deformedModelGraphMap (h m : ℝ) : G.invariantCore →ₗ[ℂ]
    FullL2 N × (SpinIndex → FullL2 N) :=
  (coreToL2.comp G.invariantCore.subtype).prod
    ((M.deformedChargeVector h m).comp G.invariantCore.subtype)

def deformedModelGraph (h m : ℝ) : Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  (LinearMap.range (G.deformedModelGraphMap h m)).topologicalClosure

lemma deformedModelGraph_le_full (h m : ℝ) :
    G.deformedModelGraph h m ≤ M.deformedClosedGraph h m := by
  apply Submodule.topologicalClosure_mono
  rintro p ⟨f,rfl⟩
  exact ⟨f.val,rfl⟩

lemma deformedModelGraph_vertical (h m : ℝ) {y : SpinIndex → FullL2 N}
    (hy : ((0 : FullL2 N),y) ∈ G.deformedModelGraph h m) : y = 0 :=
  M.deformedClosedGraph_vertical h m (G.deformedModelGraph_le_full h m hy)

lemma deformedModelGraph_coreNormClosure (h m : ℝ) {x : FullL2 N} {y : SpinIndex → FullL2 N}
    (hp : (x,y) ∈ G.deformedModelGraph h m) : x ∈ G.coreNormClosure := by
  have hc0 : IsClosed (G.coreNormClosure : Set (FullL2 N)) :=
    (LinearMap.range (coreToL2.comp G.invariantCore.subtype)).isClosed_topologicalClosure
  have hc : IsClosed {p : FullL2 N × (SpinIndex → FullL2 N) | p.1 ∈ G.coreNormClosure} :=
    hc0.preimage continuous_fst
  apply closure_minimal (s := (LinearMap.range (G.deformedModelGraphMap h m) : Set _)) _ hc hp
  rintro p ⟨f,rfl⟩
  exact (G.coreNormEmbedding f).prop

lemma deformedModelGraph_approx (h m : ℝ)
    {x : FullL2 N} {y : SpinIndex → FullL2 N} (hp : (x,y) ∈ G.deformedModelGraph h m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : G.invariantCore, dist x (coreToL2 f.val) < ε ∧
      ∀ α, dist (y α) (coreToL2 (M.deformedCoreCharge h m α f.val)) < ε := by
  obtain ⟨p,⟨f,rfl⟩,hd⟩ := Metric.mem_closure_iff.mp hp ε hε
  change max (dist x (coreToL2 f.val))
    (dist y (M.deformedChargeVector h m f.val)) < ε at hd
  refine ⟨f,(max_lt_iff.mp hd).1,?_⟩
  intro α
  exact (dist_le_pi_dist y (M.deformedChargeVector h m f.val) α).trans_lt (max_lt_iff.mp hd).2
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

theorem normalClosed_extraction (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (nhds 0))
    (x : ℕ → G.coreNormClosure) (y : ℕ → SpinIndex → FullL2 N) (B : ℝ≥0)
    (hg : ∀ n, ((x n : FullL2 N),y n) ∈ G.deformedModelGraph (h n) 1)
    (hx : ∀ n, ‖x n‖ ≤ B) (hy : ∀ n α, ‖y n α‖ ≤ B) :
    ∃ S : Finset (Boson N),
      (∀ q ∈ S, q ∈ M.massiveZeros) ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) ∧
      ∃ P : (q : S) → G.MeasuredNormalPatch q.val,
        ∃ v : (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val)),
          ∃ σ : ℕ → ℕ, StrictMono σ ∧
            (∀ q, Tendsto (fun n => (P q).closedProfile (h (σ n)) (x (σ n))) atTop (nhds (v q))) ∧
            Tendsto (fun n => ‖x (σ n)‖^2) atTop (nhds (∑ q : S, ‖v q‖^2)) := by
  classical
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεzero : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f hf hQ using (fun n => G.deformedModelGraph_approx (h n) 1 (hg n) (ε n) (hε n))
  let C : ℝ≥0 := B+1
  have hcf (n : ℕ) : ‖coreToL2 (f n).val‖ ≤ C := by
    have hd : dist (coreToL2 (f n).val) (x n : FullL2 N) ≤ 1 :=
      by rw [dist_comm]; exact (hf n).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    exact ha.trans (add_le_add (show ‖(x n : FullL2 N)‖ ≤ B from hx n) le_rfl)
  have hqf (n : ℕ) (α : SpinIndex) : ‖coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)‖ ≤ C := by
    have hd : dist (coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)) (y n α) ≤ 1 :=
      by rw [dist_comm]; exact (hQ n α).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    linarith [hy n α]
  have hfs (n : ℕ) : ‖coreToL2 (f n).val‖^2 ≤ (C^2 : ℝ≥0) :=
    pow_le_pow_left₀ (norm_nonneg _) (hcf n) 2
  have he (n : ℕ) : M.deformedCoreEnergy (h n) 1 (f n).val ≤ (C^2 : ℝ≥0) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hqf n α) 2)
    unfold AlgebraData.deformedCoreEnergy
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num only [Nat.cast_ofNat] at hs
    change _ ≤ (C : ℝ)^2
    linarith
  obtain ⟨S,hS,hcov,hdis,P,v,σ,hσ,hcoord,hnorm⟩ :=
    G.normalCore_extraction hN h hh hzero f (C^2) hfs he
  have hdist (q : S) : Tendsto (fun n => dist ((P q).profile (h n) (f n))
      ((P q).closedProfile (h n) (x n))) atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg) _ hεzero
    intro n
    exact ((P q).closedProfile_core_dist_le (hh n).1 (hh n).2 (f n) (x n)).trans
      (by rw [dist_comm]; exact (hf n).le)
  refine ⟨S,hS,hcov,hdis,P,v,σ,hσ,fun q => (hcoord q).congr_dist ((hdist q).comp hσ.tendsto_atTop),?_⟩
  have hnormdist : Tendsto (fun n => dist (‖coreToL2 (f n).val‖^2) (‖x n‖^2)) atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg)
      (g := fun n => ε n*((C : ℝ)+B)) _ (by simpa only [zero_mul] using hεzero.mul_const ((C : ℝ)+B))
    intro n
    have hd := BFSSRellich.normSquare_distance_le (coreToL2 (f n).val) (x n : FullL2 N)
    apply hd.trans
    apply mul_le_mul
    · rw [dist_comm]; exact (hf n).le
    · exact add_le_add (hcf n) (hx n)
    · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact (hε n).le
  exact hnorm.congr_dist (hnormdist.comp hσ.tendsto_atTop)
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
