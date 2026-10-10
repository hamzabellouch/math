import Mathlib
import OAI.Analysis.BoundedHochschild.CochainAverages
import OAI.Analysis.BoundedHochschild.Liouville

namespace OAI

/-! Trace preduals, primitives from averages and finite exactness. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

 

def TraceInPredual : Prop := ∃ z : X, ∀ x : M, τ x = star (e.symm x z)

omit [StarOrderedRing M] in
lemma trace_predual_tendsto (hτ : TraceInPredual e τ)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ b)) := by
  obtain ⟨z,hz⟩ := hτ
  simpa only [hz] using (h z).star

 

lemma preGNS_norm_le_of_predual_tendsto
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖τ.toPreGNS (a i)‖ ≤ C)
    (h : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ ≤ C := by
  have ht := trace_predual_tendsto e τ hτ ((hL (star b)).tendsto e h)
  have ht' : Tendsto (fun i => inner ℂ (τ.toPreGNS b) (τ.toPreGNS (a i))) l
      (𝓝 (inner ℂ (τ.toPreGNS b) (τ.toPreGNS b))) := by
    simpa only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,ContinuousLinearMap.mul_apply'] using ht
  have hb : ‖inner ℂ (τ.toPreGNS b) (τ.toPreGNS b)‖ ≤ ‖τ.toPreGNS b‖ * C := by
    apply le_of_tendsto ht'.norm
    filter_upwards [ha] with i hi
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hb
  nlinarith [norm_nonneg (τ.toPreGNS b)]

lemma preGNS_norm_unitary_right (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (x : M) (u : unitary M) : ‖τ.toPreGNS (x*(u:M))‖ = ‖τ.toPreGNS x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [PositiveLinearMap.preGNS_norm_sq,PositiveLinearMap.ofPreGNS_toPreGNS,star_mul]
  rw [mul_assoc (star (u:M))]
  rw [htr (star (u:M)) (star x*(x*(u:M)))]
  simp [mul_assoc]

end BoundedHochschild

 

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

 

theorem primitive_from_average {n : ℕ} (f F : Cochain M (n+1))
    (hF : ‖F‖ ≤ ‖f‖)
    (hr : ∀ x, residualCLM x F = ((-1:ℂ)^(n+1)) • f x)
    (hm : ∀ (a : Fin n → M) (x : M), F (Fin.snoc a x) = F (Fin.snoc a 1)*x) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  let g : Cochain M n := ((-1:ℂ)^(n+1)) • insertLast F 1
  have hnorm : ‖g‖ ≤ ‖f‖ := by
    calc
      ‖g‖ = ‖insertLast F 1‖ := by simp [g,norm_smul,norm_pow]
      _ ≤ ‖F‖ * ‖(1:M)‖ := norm_insertLast_le _ _
      _ ≤ ‖F‖ := by
        rcases subsingleton_or_nontrivial M with h | h
        · have : (1:M) = 0 := Subsingleton.elim _ _
          simp [this]
        · simp
      _ ≤ ‖f‖ := hF
  refine ⟨g,hnorm,fun x => ?_⟩
  have he : F x = insertLast F 1 (fun i : Fin n => x i.castSucc)*x (Fin.last n) := by
    have h := hm (Fin.init x) (x (Fin.last n))
    rw [Fin.snoc_init_self] at h
    exact h
  have hd : differentialValue (insertLast F 1) x = ((-1:ℂ)^(n+1)) • f x := by
    have h := hr x
    rw [residual_eq_differential,he,sub_self,smul_zero,add_zero] at h
    exact h
  change differentialValue (((-1:ℂ)^(n+1)) • insertLast F 1) x = f x
  rw [differentialValue_smul,hd,smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul]

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

lemma last_bound_average {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C) :
    ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (averageLast p u F (Fin.snoc a x))‖ ≤ C := by
  intro x hx hδ
  let L : Cochain M (n+1) →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M (Fin.snoc a x))
  have he (j : ℕ) : ‖L ((p j:ℂ) • translateLast F (u j))‖ ≤ p j*C := by
    change ‖hilbertMap τ h1 (((p j:ℂ) • translateLast F (u j)) (Fin.snoc a x))‖ ≤ _
    rw [smul_apply,map_smul,norm_smul,hilbertMap_norm,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp j)]
    apply mul_le_mul_of_nonneg_left _ (hp j)
    simp only [translateLast_apply,Fin.snoc_castSucc,Fin.snoc_last]
    have hu := trace_norm_unitary_right τ htr (F (Fin.snoc a (x*(u j:M)))) (star (u j))
    rw [show star (u j:M) = ((star (u j):unitary M):M) by rfl,hu]
    exact hF _ (by simpa only [CStarRing.norm_mul_coe_unitary] using hx)
      (by simpa only [trace_norm_unitary_right τ htr] using hδ)
  have ht := L.map_tsum (summable_averageLast p u hp hs.summable F)
  have hb := tsum_of_norm_bounded (hs.mul_right C) he
  rw [← ht] at hb
  simpa only [averageLast,ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.apply_apply,
    hilbertMap_norm,L,one_mul] using hb

lemma last_bound_iterate {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C)
    (j : ℕ) : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (((averageLastCLM p u hp hs)^[j] F) (Fin.snoc a x))‖ ≤ C := by
  induction j with
  | zero => exact hF
  | succ j ih =>
    simpa only [Function.iterate_succ_apply',averageLastCLM_apply] using
      last_bound_average τ h1 htr p u hp hs a R δ C ((averageLastCLM p u hp hs)^[j] F) ih

lemma last_bound_cesaro {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C)
    (j : ℕ) : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ ≤ C := by
  intro x hx hδ
  let L : Cochain M (n+1) →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M (Fin.snoc a x))
  have he (k : ℕ) : ‖L ((averageLastCLM p u hp hs)^[k] F)‖ ≤ C :=
    (hilbertMap_norm τ h1 _).le.trans (last_bound_iterate τ h1 htr p u hp hs a R δ C F hF k x hx hδ)
  have hb : ‖∑ k ∈ Finset.range (j+1), L ((averageLastCLM p u hp hs)^[k] F)‖ ≤ (j+1:ℝ)*C := by
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1), ‖L ((averageLastCLM p u hp hs)^[k] F)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range (j+1), C := Finset.sum_le_sum fun k _ => he k
      _ = _ := by simp [nsmul_eq_mul]
  have hj : (j+1:ℝ) ≠ 0 := by positivity
  have heq : ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ =
      ‖L (HochschildCesaro.avg (averageLastCLM p u hp hs) F j)‖ := (hilbertMap_norm τ h1 _).symm
  rw [heq,HochschildCesaro.avg,map_smul,map_sum,norm_smul,norm_inv,
    ← Nat.cast_add_one,Complex.norm_natCast,Nat.cast_add_one]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
    rw [← mul_assoc,inv_mul_cancel₀ hj,one_mul])

 

theorem cesaro_limit_last_modulus {n : ℕ}
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ)
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (F G : Cochain M (n+1)) (U : Ultrafilter ℕ)
    (ht : ∀ x, PredualTendsto e
      (fun j => HochschildCesaro.avg (averageLastCLM p u hp hs) F j x) U (G x))
    (hF : ∀ a : Fin n → M, BallModulus τ.toPreGNS (F.curryRight a)) :
    ∀ a : Fin n → M, BallModulus τ.toPreGNS (G.curryRight a) := by
  intro a R ε hε
  obtain ⟨δ,hδ,hm⟩ := hF a R (ε/2) (half_pos hε)
  refine ⟨δ,hδ,fun x hx hxδ => ?_⟩
  have hb (j : ℕ) : ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ ≤ ε/2 :=
    last_bound_cesaro τ h1 htr p u hp hs a R δ (ε/2) F
      (fun y hy hyδ => (hm y hy hyδ).le) j x hx hxδ
  exact (preGNS_norm_le_of_predual_tendsto e τ hL hτ (ε/2) (half_pos hε).le
    (Eventually.of_forall hb) (ht (Fin.snoc a x))).trans_lt (half_lt_self hε)

end BoundedHochschild

 

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

def atomicLaw (p : ℕ → ℝ) (a : ℕ → G) : Measure G :=
  Measure.sum (fun j => ENNReal.ofReal (p j) • Measure.dirac (a j))

omit [MeasurableSingletonClass G] in
lemma atomicLaw_probability (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (a : ℕ → G) : IsProbabilityMeasure (atomicLaw p a) := by
  constructor
  simp only [atomicLaw,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hp hs.summable,hs.tsum_eq,ENNReal.ofReal_one]

lemma integral_atomicLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : Summable p)
    (a : ℕ → G) (f : G → E) (C : ℝ) (hf : ∀ j, ‖f (a j)‖ ≤ C) :
    ∫ g, f g ∂atomicLaw p a = ∑' j, p j • f (a j) := by
  have hs' : Summable (fun j => (ENNReal.ofReal (p j)).toReal * ‖f (a j)‖) := by
    simp only [ENNReal.toReal_ofReal (hp _)]
    apply (hs.mul_right C).of_nonneg_of_le (fun j => mul_nonneg (hp j) (norm_nonneg _))
    exact fun j => mul_le_mul_of_nonneg_left (hf j) (hp j)
  simpa only [atomicLaw,ENNReal.toReal_ofReal (hp _)] using
    integral_sum_dirac_eq_tsum (f := f) (x := a) (fun j => ENNReal.ofReal_ne_top) hs'

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

lemma average_fixed_harmonic {n : ℕ} (ρ : G →* unitary M)
    (p : ℕ → ℝ) (atoms : ℕ → G) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (F : Cochain M (n+1)) (hF : averageLast p (fun j => ρ (atoms j)) F = F)
    (a : Fin n → M) (x : M) :
    ∫ u, (F.curryRight a) (x*(ρ u:M)) * (ρ u⁻¹:M) ∂atomicLaw p atoms = (F.curryRight a) x := by
  have hb (j : ℕ) : ‖(F.curryRight a) (x*(ρ (atoms j):M)) * (ρ (atoms j)⁻¹:M)‖ ≤
      ‖F.curryRight a‖ * ‖x‖ := by
    rw [CStarRing.norm_mul_coe_unitary]
    exact ((F.curryRight a).le_opNorm _).trans_eq (by rw [CStarRing.norm_mul_coe_unitary])
  rw [integral_atomicLaw p hp hs.summable atoms _ _ hb]
  have he := congrArg (fun H : Cochain M (n+1) => H (Fin.snoc a x)) hF
  rw [averageLast_apply p _ hp hs.summable] at he
  convert he using 1
  · apply tsum_congr
    intro j
    simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,map_inv]
    rw [← algebraMap_smul ℝ (p j)]
    rfl
  · rfl

end BoundedHochschild

 

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

 

theorem primitive_of_walk_and_last_modulus
    (h1 : τ 1 = 1) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ)
    (ρ : G →* unitary M) (p : ℕ → ℝ) (atoms : ℕ → G)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (hsym : (atomicLaw p atoms).map (fun g => g⁻¹) = atomicLaw p atoms)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability (atomicLaw p atoms) (fun g => ‖τ (ρ g : M)‖) time)
    (hdense : ∀ u : unitary M, ∃ g : ℕ → G, (∀ j, atomicLaw p atoms {g j} ≠ 0) ∧
      Tendsto (fun j => ‖τ.toPreGNS ((ρ (g j):M)-(u:M))‖) atTop (𝓝 0))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0)
    (hmod : ∀ a : Fin n → M, BallModulus τ.toPreGNS (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  let : IsProbabilityMeasure (atomicLaw p atoms) := atomicLaw_probability p hp hs atoms
  obtain ⟨F,hF,hfix,hres,U,_hU,ht⟩ :=
    exists_average_fixed_cocycle e hL hR p (fun j => ρ (atoms j)) hp hs f hf
  have hFm := cesaro_limit_last_modulus τ h1 htr e hL hτ p (fun j => ρ (atoms j)) hp hs f F U ht hmod
  apply primitive_from_average f F hF hres
  intro a x
  have hh := hilbertD_harmonic τ h1 ρ (F.curryRight a) (atomicLaw p atoms)
    (average_fixed_harmonic ρ p atoms hp hs F hfix a)
  exact multiplier_of_walk τ h1 htr hfaith ρ (F.curryRight a) (atomicLaw p atoms)
    ((ballSequential_iff_modulus τ.toPreGNS (F.curryRight a)).mpr (hFm a))
    hsym time htime hmom hh hdense x

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_differential
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  simp only [differentialValue]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e ((hR (x (Fin.last n))).tendsto e (ht _)) _

 

theorem primitive_of_finite_exactness
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {n : ℕ} (f : Cochain M (n+1)) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ E : Finset M, ∃ g : Cochain M n, ‖g‖ ≤ C ∧
      ∀ x : Fin (n+1) → M, (∀ i, x i ∈ E) → differentialValue g x = f x) :
    ∃ g : Cochain M n, ‖g‖ ≤ C ∧ ∀ x : Fin (n+1) → M, differentialValue g x = f x := by
  classical
  choose F hF hFE using hlocal
  let U : Ultrafilter (Finset M) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset M)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g,hg,ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  refine ⟨g,hg,fun x => ?_⟩
  have hd := predual_tendsto_differential e hL hR ht x
  have hex : (fun E => differentialValue (F E) x) =ᶠ[U] (fun _ => f x) := by
    apply hU
    filter_upwards [eventually_ge_atTop (Finset.univ.image x)] with E hE
    exact hFE E x fun i => hE (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  apply predual_tendsto_unique e hd
  intro z
  exact tendsto_const_nhds.congr' (hex.mono fun _ h => congrArg (fun a : M => e.symm a z) h.symm)

end BoundedHochschild
end

end OAI
