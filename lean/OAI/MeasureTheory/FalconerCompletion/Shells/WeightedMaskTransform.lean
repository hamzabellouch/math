import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.OutgoingWeightedKernelNorm
import OAI.MeasureTheory.FalconerCompletion.Shells.ContinuousCoefficientMeasurableSquare
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellPolynomialSubpower

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate Topology ContDiff
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

noncomputable def weightedMaskTransformND (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (ρ ν : Measure V) (X Y : Set V) (M N a r : ℝ) : ℂ :=
  ((M*N)⁻¹:ℝ) • (∫ z, (F z.1*conj (G z.2))*
    outgoingWeightedKernelND r ((2:ℝ)^a) (pairMaskProductND S T f g) z
      ∂(ρ.restrict X).prod (ν.restrict Y))

theorem weighted_all_mask_shellND (ψ : V → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (η T₀ C₀ : ℝ) (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    ∃ J : ℕ, ∃ Error : ℝ, 0 ≤ Error ∧ ∀
      (S : Finset ι) (T : Finset κ)
      (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
      (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ),
      (∀ i ∈ S, 0 < D i) → (∀ k ∈ T, 0 < E k) → ∀
      (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
      (ρ ν : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
      (X Y : Set V), MeasurableSet X → MeasurableSet Y → ∀
      (M N R A Q a v : ℝ), 1 ≤ R → 1 ≤ A → A ≤ R^2 → 1 ≤ Q →
      (2:ℝ)^(-(v-a))*Q^2 ≤ 1 →
      (∀ i ∈ S, D i ≤ Q) → (∀ k ∈ T, E k ≤ Q) →
      (∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y*(2:ℝ)^a ∧ dist x y*(2:ℝ)^a ≤ K) →
      (∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
        R^η ≤ r*dist z.1 z.2 ∧ A^2/(r*dist z.1 z.2) ≤ R^(-η) ∧
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) ∧
        (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
          ‖iteratedFDeriv ℝ k (pairMaskProductND S T f g z).1 w‖ ≤ C₀*A^k)) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), ‖F z.1*conj (G z.2)‖ ≤ 1) →
      Measurable (fun z => (F z.1*conj (G z.2))*
        (pairMaskProductND S T f g z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))) →
      ∀ (P : ℝ), (∀ w, ‖ψ w‖ ≤ P) → ∀ (B C : ℕ → Assignment → ℝ),
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseLeftEndpointND S D f F p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseRightEndpointND T E g G p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ x w,
        ‖inverseLeftEndpointND S D f F p x w‖ ≤ B j p) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ y w,
        ‖inverseRightEndpointND T E g G p y w‖ ≤ C j p) →
      ∀ (Ψ : ℝ → ℝ), Integrable (fun r => Ψ (r/(2:ℝ)^v)) →
      (∀ r, 0 ≤ Ψ r) → (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) → ∀ (BHF : ℝ), 0 ≤ BHF →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ ξ,
        sourceAngularHFND (n+1) (canonicalSphereMeasureND V) a v Ψ ψ
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ρ X M
            (inverseLeftEndpointND S D f F p) (ξ,z))
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ν Y N
            (inverseRightEndpointND T E g G p) (ξ,z)) ≤ BHF) →
      Integrable (fun r => ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2)
        (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
        ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2) ≤
        2*(fullInverseCoefficientCostND n J δ K hδ hK*
          (max 1 ((S.card+T.card:ℕ):ℝ))^(2*J))^2*BHF +
        3*(2:ℝ)^(v-a)*
          (|(M*N)⁻¹| * ((δ^(-(n:ℝ)/2)*Error*R^(-T₀))*
            ((ρ.restrict X).prod (ν.restrict Y)).real univ))^2 := by
  obtain ⟨J,Error,hError,hInv⟩ := all_mask_weighted_inverseND (ι := ι) (κ := κ) ψ hψ η T₀ C₀ hη hC₀
  refine ⟨J,Error,hError,?_⟩
  intro S T f g F G D E hD hE δ K hδ hK ρ ν hρ hν X Y hX hY
    M N R A Q a v hR hA hup hQ hpaid hDQ hEQ hsep hgeom hFG hsym
    P hP B C hb hc hB hC Ψ hΨ hΨpos hone BHF hBHF hHF
  let μ := (ρ.restrict X).prod (ν.restrict Y)
  let L := inverseTermListND (n := n) J S T
  let cc : (ℕ × Assignment) → V → ℂ := fun p =>
    paidSpatialCoefficientND p.1 S T D E ((2:ℝ)^(-(v-a))) δ K hδ hK p.2
  let mm : (ℕ × Assignment) → ℝ → ℂ := fun p => shellRadialMultiplierND n p.1 v
  let U : (ℕ × Assignment) → V × (ℝ × V) → ℂ := fun p =>
    spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ρ X M (inverseLeftEndpointND S D f F p.2)
  let W : (ℕ × Assignment) → V × (ℝ × V) → ℂ := fun p =>
    spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ν Y N (inverseRightEndpointND T E g G p.2)
  let AA : (ℕ × Assignment) → ℝ := fun p => (2:ℝ)^((n:ℝ)/2)*(2:ℝ)^p.1
  let BB : (ℕ × Assignment) → ℝ := fun p => |M⁻¹| * (|B p.1 p.2| *(ρ.restrict X).real univ)
  let CC : (ℕ × Assignment) → ℝ := fun p => |N⁻¹| * (|C p.1 p.2| *(ν.restrict Y).real univ)
  let H := weightedMaskTransformND S T f g F G ρ ν X Y M N a
  have hs : 0 < (2:ℝ)^a := Real.rpow_pos_of_pos (by norm_num) _
  have hxy : ∀ᵐ z ∂μ, z.1 ∈ X ∧ z.2 ∈ Y :=
    (Measure.ae_prod_iff_ae_ae (hX.prod hY)).mpr (by
      filter_upwards [ae_restrict_mem hX] with x hx
      filter_upwards [ae_restrict_mem hY] with y hy
      exact ⟨hx,hy⟩)
  have hδs : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2*(2:ℝ)^a := by
    filter_upwards [hxy] with z hz
    exact (hsep z.1 hz.1 z.2 hz.2).1
  have hraw (r : ℝ) (hr : r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v)) :
      Integrable (fun z => (F z.1*conj (G z.2))*
        outgoingWeightedKernelND r ((2:ℝ)^a) (pairMaskProductND S T f g) z) μ := by
    apply outgoingWeightedKernelND_integrable ((2:ℝ)^a) hs _ _ μ r hδ hδs hsym
    filter_upwards [hδs,hgeom r hr,hFG] with z hz hg hfg
    have hd : 0 < dist z.1 z.2 := (mul_pos_iff_of_pos_right hs).mp (hδ.trans_le hz)
    have he : ‖(dist z.1 z.2)⁻¹ • (z.1-z.2)‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hd,← dist_eq_norm,inv_mul_cancel₀ hd.ne']
    have hb₀ := hg.2.2.2.2 0 (Nat.zero_le _) _ he
    simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hb₀
    rw [norm_mul]
    exact (mul_le_mul hfg hb₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have hH : Measurable H := weighted_pair_integral_measurableND ((2:ℝ)^a)
    (pairMaskProductND S T f g) (fun z => F z.1*conj (G z.2)) μ ((M*N)⁻¹) hsym
  have happrox (r : ℝ) (hr : r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v)) :
      ‖H r-(((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*
        (L.map (fun p => mm p r*∫ ξ, cc p ξ*sourceAngularCorrelationND
          (canonicalSphereMeasureND V) ψ (fun z => U p (ξ,z)) (fun z => W p (ξ,z)) r)).sum‖ ≤
      |(M*N)⁻¹| * ((δ^(-(n:ℝ)/2)*Error*R^(-T₀))*μ.real univ) := by
    have hrp : 0 < r := (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).trans_le hr.1
    have hh := hInv S T f g F G D E (fun i hi => (hD i hi).ne') (fun k hk => (hE k hk).ne')
      δ K hδ hK ρ ν X Y hX hY M N R A r ((2:ℝ)^a) hrp hs hR hA hup hsep
      (hgeom r hr) hFG (hraw r hr) P hP B C hb hc hB hC
    rw [all_mask_shell_factorizationND J S T f g F G D E δ K hδ hK ρ ν X Y M N a v r hrp ψ] at hh
    exact hh
  have hmemb (p : ℕ × Assignment) (hp : p ∈ L) := (mem_inverseTermListND J S T p).mp hp
  have hU (p : ℕ × Assignment) (hp : p ∈ L) : Measurable (U p) :=
    spatialEndpointTransformND_measurable _ _ _ _ (hb p.1 (hmemb p hp).1 p.2 (hmemb p hp).2)
  have hW (p : ℕ × Assignment) (hp : p ∈ L) : Measurable (W p) :=
    spatialEndpointTransformND_measurable _ _ _ _ (hc p.1 (hmemb p hp).1 p.2 (hmemb p hp).2)
  have hbU (p : ℕ × Assignment) (hp : p ∈ L) (ξ : V) (r : ℝ) (w : V) :
      ‖U p (ξ,(r,w))‖ ≤ BB p :=
    spatialEndpointTransformND_bound _ _ _ _ _
      (fun x w => (hB p.1 (hmemb p hp).1 p.2 (hmemb p hp).2 x w).trans (le_abs_self _)) _
  have hbW (p : ℕ × Assignment) (hp : p ∈ L) (ξ : V) (r : ℝ) (w : V) :
      ‖W p (ξ,(r,w))‖ ≤ CC p :=
    spatialEndpointTransformND_bound _ _ _ _ _
      (fun x w => (hC p.1 (hmemb p hp).1 p.2 (hmemb p hp).2 x w).trans (le_abs_self _)) _
  have hh := full_HF_shell_mixtureND n volume (canonicalSphereMeasureND V) a v L cc mm ψ U W H AA BB CC
    (fun _ _ => by dsimp [AA]; positivity)
    (fun p _ => paidSpatialCoefficientND_measurable p.1 S T D E _ δ K hδ hK p.2)
    (fun p _ => paidSpatialCoefficientND_integrable p.1 S T D E _ δ K hδ hK p.2)
    (fun p _ => shellRadialMultiplierND_measurable n p.1 v)
    (fun p _ _ hr => shellRadialMultiplierND_bound n p.1 hr)
    hψ.continuous.measurable hU hW (abs_nonneg P)
    (fun _ _ => by dsimp [BB]; positivity) (fun w => (hP w).trans (le_abs_self P)) hbU hbW
    hΨ hΨpos hone (fun p hp ξ => hHF p.1 (hmemb p hp).1 p.2 (hmemb p hp).2 ξ)
    hH.aestronglyMeasurable happrox
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ hBHF
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply pow_le_pow_left₀
  · apply List.sum_nonneg
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (by dsimp [AA]; positivity) (integral_nonneg (fun _ => norm_nonneg _))
  · exact inverseTermListND_paid_cost J S T D E hQ (by positivity) hpaid
      (fun i hi => (hD i hi).le) (fun k hk => (hE k hk).le) hDQ hEQ δ K hδ hK

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter Real
open scoped Topology

theorem shell_polynomial_subpowerND (k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, C*(N:ℝ)^k ≤ ((2:ℝ)^N)^ε := by
  have hr : 1<(2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hr).const_mul C
  have hh : ∀ᶠ N : ℕ in atTop, C*((N:ℝ)^k/((2:ℝ)^ε)^N) ≤ 1 := by
    have hc := ht.eventually_lt_const (show C*0 < (1:ℝ) by simp)
    exact hc.mono (fun _ h => h.le)
  filter_upwards [hh] with N hN
  have he : ((2:ℝ)^ε)^N=((2:ℝ)^N)^ε := by
    rw [← Real.rpow_natCast ((2:ℝ)^ε) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),mul_comm ε]
  rw [← mul_div_assoc] at hN
  exact ((div_le_one (by positivity)).mp hN).trans_eq he

theorem shell_mask_cost_subpowerND (J k : ℕ) (D C ε : ℝ) (hD : 0≤D)
    (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ P : ℝ, 0≤P → P≤C*(N:ℝ)^k →
      2*(D*P^(2*J))^2 ≤ ((2:ℝ)^N)^ε := by
  filter_upwards [shell_polynomial_subpowerND (k*(4*J)) (2*D^2*C^(4*J)) ε hε] with N hN
  intro P hP hPC
  calc
    _ ≤ 2*(D*(C*(N:ℝ)^k)^(2*J))^2 := by gcongr
    _ = (2*D^2*C^(4*J))*(N:ℝ)^(k*(4*J)) := by
      simp only [mul_pow,← pow_mul]
      have he : 2*J*2=4*J := by omega
      simp only [Nat.mul_assoc,he]
      ring
    _ ≤ _ := hN

lemma shell_dyadic_tendstoND : Tendsto (fun N : ℕ => (2:ℝ)^N) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma shell_eventually_const_mul_rpowND {a b C : ℝ} (hab : a < b) :
    ∀ᶠ R : ℝ in atTop, C*R^a ≤ R^b := by
  have ht : Tendsto (fun R : ℝ => C*R^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C
    simpa only [neg_sub,mul_zero] using hh
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1),
    eventually_gt_atTop (0:ℝ)] with R hR hRp
  have he : C*R^a = (C*R^(a-b))*R^b := by
    rw [mul_assoc,← Real.rpow_add hRp]
    congr 2
    ring
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hR.le (Real.rpow_nonneg hRp.le _)

theorem shell_mass_error_decayND (B T C : ℝ) (hC : 0≤C) :
    ∀ᶠ R : ℝ in atTop, ∀ (q H : ℝ), 0≤H → H≤R^B → (2:ℝ)^q ≤ R^2 →
      3*(2:ℝ)^q*(C*R^(-(T/2+B+2))*H)^2 ≤ R^(-T) := by
  filter_upwards [shell_eventually_const_mul_rpowND (C := 3*C^2)
    (show -T-2 < -T by linarith),eventually_gt_atTop (0:ℝ)] with R hR hRp
  intro q H hH hHB hq
  calc
    _ ≤ 3*R^2*(C*R^(-(T/2+B+2))*R^B)^2 := by gcongr
    _ = (3*C^2)*R^(-T-2) := by
      rw [mul_pow,mul_pow,← Real.rpow_natCast (R^(-(T/2+B+2))) 2,
        ← Real.rpow_mul hRp.le,← Real.rpow_natCast (R^B) 2,← Real.rpow_mul hRp.le,
        ← Real.rpow_natCast R 2]
      calc
        _ = (3*C^2)*(R^(2:ℝ)*(R^(-(T/2+B+2)*(2:ℝ))*R^(B*(2:ℝ)))) := by ring_nf
        _ = _ := by rw [← Real.rpow_add hRp,← Real.rpow_add hRp]; congr 2; ring
    _ ≤ _ := hR
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate Topology ContDiff
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

theorem weighted_all_mask_shell_asymptoticND (ψ : V → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (kCard : ℕ) (η C₀ ε T₀ Bmass Cmask δ K : ℝ) (hη : 0 < η) (hC₀ : 0 ≤ C₀)
    (hε : 0<ε) (hδ : 0<δ) (hK : 0<K) :
    ∃ J : ℕ, ∀ᶠ kN : ℕ in Filter.atTop, let R := (2:ℝ)^kN; ∀
      (S : Finset ι) (T : Finset κ)
      (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
      (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ),
      (∀ i ∈ S, 0 < D i) → (∀ k ∈ T, 0 < E k) →
      max 1 ((S.card+T.card:ℕ):ℝ) ≤ Cmask*(kN:ℝ)^kCard → ∀ (ρ ν : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
      (X Y : Set V), MeasurableSet X → MeasurableSet Y → ∀
      (M N A Q a v : ℝ), 1 ≤ A → A ≤ R^2 → 1 ≤ Q →
      (2:ℝ)^(v-a) ≤ R^2 →
      |(M*N)⁻¹| * ((ρ.restrict X).prod (ν.restrict Y)).real univ ≤ R^Bmass →
      (2:ℝ)^(-(v-a))*Q^2 ≤ 1 →
      (∀ i ∈ S, D i ≤ Q) → (∀ k ∈ T, E k ≤ Q) →
      (∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y*(2:ℝ)^a ∧ dist x y*(2:ℝ)^a ≤ K) →
      (∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
        R^η ≤ r*dist z.1 z.2 ∧ A^2/(r*dist z.1 z.2) ≤ R^(-η) ∧
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) ∧
        (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
          ‖iteratedFDeriv ℝ k (pairMaskProductND S T f g z).1 w‖ ≤ C₀*A^k)) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), ‖F z.1*conj (G z.2)‖ ≤ 1) →
      Measurable (fun z => (F z.1*conj (G z.2))*
        (pairMaskProductND S T f g z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))) →
      ∀ (P : ℝ), (∀ w, ‖ψ w‖ ≤ P) → ∀ (B C : ℕ → Assignment → ℝ),
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseLeftEndpointND S D f F p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseRightEndpointND T E g G p))) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ x w,
        ‖inverseLeftEndpointND S D f F p x w‖ ≤ B j p) →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ y w,
        ‖inverseRightEndpointND T E g G p y w‖ ≤ C j p) →
      ∀ (Ψ : ℝ → ℝ), Integrable (fun r => Ψ (r/(2:ℝ)^v)) →
      (∀ r, 0 ≤ Ψ r) → (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) → ∀ (BHF : ℝ), 0 ≤ BHF →
      (∀ j ≤ J, ∀ p ∈ inverseAngularTermsND j (S.disjSum T), ∀ ξ,
        sourceAngularHFND (n+1) (canonicalSphereMeasureND V) a v Ψ ψ
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ρ X M
            (inverseLeftEndpointND S D f F p) (ξ,z))
          (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ν Y N
            (inverseRightEndpointND T E g G p) (ξ,z)) ≤ BHF) →
      Integrable (fun r => ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2)
        (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
        ‖weightedMaskTransformND S T f g F G ρ ν X Y M N a r‖^2) ≤
        R^ε*BHF+R^(-T₀) := by
  obtain ⟨J,Error,hError,hMain⟩ := weighted_all_mask_shellND (ι := ι) (κ := κ)
    ψ hψ η (T₀/2+Bmass+2) C₀ hη hC₀
  refine ⟨J,?_⟩
  filter_upwards [shell_mask_cost_subpowerND J kCard (fullInverseCoefficientCostND n J δ K hδ hK)
      Cmask ε (fullInverseCoefficientCostND_nonneg n J δ K hδ hK) hε,
    shell_dyadic_tendstoND.eventually (shell_mass_error_decayND Bmass T₀
      (δ^(-(n:ℝ)/2)*Error) (mul_nonneg (Real.rpow_nonneg hδ.le _) hError))]
    with kN hcost herror
  dsimp only
  intro S T f g F G D E hD hE hcard ρ ν hρ hν X Y hX hY M N A Q a v
    hA hup hQ hq hmass hpaid hDQ hEQ hsep hgeom hFG hsym P hP B C hb hc hB hC
    Ψ hΨ hΨpos hone BHF hBHF hHF
  have hR : 1 ≤ (2:ℝ)^kN := one_le_pow₀ (by norm_num)
  obtain ⟨hint,hbound⟩ := hMain S T f g F G D E hD hE δ K hδ hK ρ ν X Y hX hY
    M N ((2:ℝ)^kN) A Q a v hR hA hup hQ hpaid hDQ hEQ hsep hgeom hFG hsym
    P hP B C hb hc hB hC Ψ hΨ hΨpos hone BHF hBHF hHF
  refine ⟨hint,hbound.trans (add_le_add ?_ ?_)⟩
  · exact mul_le_mul_of_nonneg_right (hcost _ (le_trans zero_le_one (le_max_left _ _)) hcard) hBHF
  · simpa only [mul_assoc,mul_left_comm,mul_comm] using herror (v-a) (|(M*N)⁻¹| * ((ρ.restrict X).prod (ν.restrict Y)).real univ)
      (mul_nonneg (abs_nonneg _) (measureReal_nonneg)) hmass hq

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
