import Mathlib
import OAI.Analysis.HardSphere.Collisions.IteratedInsertion
import OAI.Analysis.HardSphere.Collisions.IntegrableCompInsertNth
import OAI.Analysis.HardSphere.Geometry.ScalarPartitionIms

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partition_error_integral {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (u : ScalarL2 n L) :
    (∑ p : Direction n, ∑ s, ‖(w s).derivativeScalar p u‖^2)=
      ∫ X, (∑ p : Direction n, ∑ s, ‖coordDerivative n L (w s).toFun p X‖^2)*‖u X‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral]
  have hi (p : Direction n) (s : S) :
      Integrable (fun X ↦ ‖((w s).derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [← integral_finsetSum Finset.univ (fun s _ ↦ hi _ s)]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ integrable_finsetSum _ (fun s _ ↦ hi p s))]
  have hc : ∀ᵐ X ∂volume, ∀ p s, ((w s).derivativeScalar p u) X=
      coordDerivative n L (w s).toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ ae_all_iff.mpr (fun s ↦ (w s).coe_derivativeScalar p u))
  apply integral_congr_ae
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow]
  simp only [Finset.sum_mul]

theorem productPartition_ims {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : Jet n L) :
    (∑ σ : Fin n → Bool, energy ((productPartition n L a c σ).onJet u))=
      energy u+∫ X, (∑ i : Fin n, ∑ j : Fin 3,
        (‖coordDerivative 1 L a.toFun (0,j) (fun _ ↦ X i)‖^2+
         ‖coordDerivative 1 L c.toFun (0,j) (fun _ ↦ X i)‖^2))*‖u.1 X‖^2 := by
  rw [SmoothMultiplier.partition_ims _ (productPartition_real a c ha hc)
    (productPartition_unity a c hp),SmoothMultiplier.partition_error_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun X ↦ by
    simp_rw [productPartition_gradient_partition a c ha hc hp]
    rw [Fintype.sum_prod_type]

lemma productPartition_norm_partition {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : ScalarL2 n L) :
    (∑ σ : Fin n → Bool, ‖(productPartition n L a c σ).onScalar u‖^2)=‖u‖^2 :=
  SmoothMultiplier.partition_scalar_norm _ (productPartition_real a c ha hc)
    (productPartition_unity a c hp) u

lemma binary_product_membership {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool → ℝ) (j : I) (hf : ∀ i, f i true+f i false=1) :
    (∑ σ : I → Bool, (if σ j then (1:ℝ) else 0)*(∏ i, f i (σ i)))=f j true := by
  have he (σ : I → Bool) : (if σ j then (1:ℝ) else 0)*(∏ i, f i (σ i))=
      (∏ i∈Finset.univ.erase j, f i (σ i))*(if σ j then f j true else 0) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun i ↦ f i (σ i)) (Finset.mem_univ j)]
    cases σ j <;> simp
  simp_rw [he]
  simpa using binary_product_sum f (fun b ↦ if b then f j true else 0) j hf

lemma productPartition_selected_probability {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) (i : Fin n) :
    (∑ σ : Fin n → Bool, (if σ i then (1:ℝ) else 0)*‖(productPartition n L a c σ).toFun X‖^2)=
      ‖a.orbital (X i)‖^2 := by
  simp_rw [productPartition_apply,norm_prod,← Finset.prod_pow]
  apply binary_product_membership (fun j b ↦ ‖(cond b a c).orbital (X j)‖^2) i
  intro j
  change ‖a.orbital (X j)‖^2+‖c.orbital (X j)‖^2=1
  rw [real_norm_sq (a.orbital (X j)) (ha (fun _ ↦ X j)),
    real_norm_sq (c.orbital (X j)) (hc (fun _ ↦ X j)),← Complex.add_re,hp,Complex.one_re]

theorem productPartition_removal_cost {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : ScalarL2 n L) :
    (∑ σ : Fin n → Bool, (∑ i : Fin n, if σ i then (1:ℝ) else 0)*
      ‖(productPartition n L a c σ).onScalar u‖^2)=
      ∫ X, (∑ i : Fin n, ‖a.orbital (X i)‖^2)*‖u X‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral,← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun σ _ ↦
    ((Lp.memLp ((productPartition n L a c σ).onScalar u)).integrable_norm_pow (by norm_num)).const_mul _)]
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, ((productPartition n L a c σ).onScalar u) X=
      (productPartition n L a c σ).toFun X*u X :=
    ae_all_iff.mpr (fun _ ↦ SmoothMultiplier.coe_onScalar _ _)
  apply integral_congr_ae
  filter_upwards [hcoe] with X hX
  simp_rw [hX,norm_mul,mul_pow,← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [productPartition_selected_probability a c ha hc hp]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

noncomputable def selectedEnergy {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (u : Jet n L) : ℝ := ∑ i : {i // p i}, ∑ q : Fin 3, ‖u.2 (i.val,q)‖^2

lemma continuous_selectedEnergy {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] :
    Continuous (selectedEnergy (L:=L) p) :=
  continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
    (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2))

def selectedAllEquiv {n : ℕ} (p : Fin n → Prop) (hp : ∀ i, p i) : {i // p i} ≃ Fin n :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,fun i ↦ ⟨⟨i,hp i⟩,rfl⟩⟩

lemma selectedEnergy_all {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i, p i) (u : Jet n L) : selectedEnergy p u=energy u := by
  rw [selectedEnergy,energy,Fintype.sum_prod_type]
  exact Fintype.sum_equiv (selectedAllEquiv p hp) _ _ (fun _ ↦ rfl)

def selectedDeleteEquiv {n : ℕ} (p : Fin (n+1) → Prop) (j : Fin (n+1)) (hj : ¬p j) :
    {i : Fin n // p (j.succAbove i)} ≃ {i : Fin (n+1) // p i} :=
  Equiv.ofBijective (fun i ↦ ⟨j.succAbove i.val,i.property⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro x
      have hx : x.val≠j := by intro h; exact hj (h ▸ x.property)
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hx
      refine ⟨⟨i,hi ▸ x.property⟩,?_⟩
      exact Subtype.ext hi)

lemma SmoothTest.selected_slice_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (p : Fin n → Prop) [DecidablePred p] (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ selectedEnergy p (f.slice j x).jet) volume :=
  integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (i.val,q)))

lemma SmoothTest.integral_selected_slice {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (p : Fin (n+1) → Prop) [DecidablePred p]
    (j : Fin (n+1)) (hj : ¬p j) :
    (∫ x : Torus L, selectedEnergy (fun i ↦ p (j.succAbove i)) (f.slice j x).jet)=selectedEnergy p f.jet := by
  simp only [selectedEnergy]
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (i.val,q)))]
  simp_rw [integral_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (_,q)),
    f.integral_slice_partial]
  exact Fintype.sum_equiv (selectedDeleteEquiv p j hj) _ _ (fun _ ↦ rfl)

theorem selected_rayleigh (n : ℕ) :
    ∀ (k : ℕ) (L : Length) (a c : ℝ),
      (∀ v : Jet k L, v∈dirichletDomain k L a → c*‖v.1‖^2≤energy v) →
    ∀ (p : Fin n → Prop) [DecidablePred p], Fintype.card {i // p i}=k →
    ∀ u : Jet n L, u∈dirichletDomain n L a → c*‖u.1‖^2≤ selectedEnergy p u := by
  induction n with
  | zero =>
    intro k L a c h p _ hp u hu
    have hk : k=0 := by simpa using hp.symm
    rw [hk] at h
    simpa [selectedEnergy,energy,Direction] using h u hu
  | succ n ih =>
    intro k L a c h p _ hp u hu
    by_cases hall : ∀ i, p i
    · have hk : k=n+1 := by
        rw [←hp,Fintype.card_congr (selectedAllEquiv p hall),Fintype.card_fin]
      rw [hk] at h
      rw [selectedEnergy_all p hall]
      exact h u hu
    · obtain ⟨j,hj⟩ := not_forall.mp hall
      have hk : Fintype.card {i : Fin n // p (j.succAbove i)}=k :=
        (Fintype.card_congr (selectedDeleteEquiv p j hj)).trans hp
      have htest (f : SmoothTest (n+1) L a) : c*‖f.jet.1‖^2≤ selectedEnergy p f.jet := by
        have hh := integral_mono ((f.slice_norm_sq_integrable j).const_mul c)
          (f.selected_slice_integrable (fun i ↦ p (j.succAbove i)) j)
          (fun x ↦ ih k L a c h (fun i ↦ p (j.succAbove i)) hk
            (f.slice j x).jet (subset_closure ⟨f.slice j x,rfl⟩))
        rw [integral_const_mul,f.integral_slice_norm_sq,f.integral_selected_slice p j hj] at hh
        exact hh
      have hc : IsClosed {u : Jet (n+1) L | c*‖u.1‖^2≤ selectedEnergy p u} :=
        isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2)) (continuous_selectedEnergy p)
      exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact htest f) hu

theorem selected_ground_removal : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (p : Fin n → Prop) [DecidablePred p],
    ∀ u : Jet n L, u∈dirichletDomain n L r →
      (energy g-C*((n-Fintype.card {i // p i}:ℕ):ℝ)*(n:ℝ)*r/L.val^3)*‖u.1‖^2≤ selectedEnergy p u := by
  obtain ⟨C,hC,hrem⟩ := ground_energy_removal
  refine ⟨C,hC,?_⟩
  intro n L r hr hs g hg p _ u hu
  let k := Fintype.card {i // p i}
  have hk : k≤n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun i : {i // p i} ↦ i.val) Subtype.val_injective
  have he : k+(n-k)=n := Nat.add_sub_of_le hk
  have h := hrem k (n-k) L r hr
  rw [he] at h
  exact selected_rayleigh n k L r _ (h hs g hg) p rfl u hu

end HardSphere

end

end OAI
