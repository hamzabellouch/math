import OAI.GroupTheory.Kervaire.Traversal

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFlow

section
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

def antisymmetric (θ : Equiv.Perm D) : Submodule ℝ (D → ℝ) where
  carrier := {γ | ∀ d, γ (θ d) = -γ d}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy d
    change x (θ d) + y (θ d) = -(x d + y d)
    rw [hx d, hy d, neg_add]
  smul_mem' := by
    intro r x hx d
    change r • x (θ d) = -(r • x d)
    rw [hx d, smul_neg]

/-- Literal sum of corner phases on each boundary circle. -/
def divergence (b : D → Z) : (D → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun γ z := ∑ d, if b d = z then γ d else 0
  map_add' γ δ := by
    ext z
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp
  map_smul' r γ := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp

omit [Fintype Z] in
lemma divergence_single (b : D → Z) (d : D) (c : ℝ) :
    divergence b (Pi.single d c) = Pi.single (b d) c := by
  ext z
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single d]
  · simp [Pi.single_apply, eq_comm]
  · intro e _ he
    simp [he]
  · simp

/-- Supported on the two ends of one band, including the harmless loop case. -/
def edgeFlow (θ : Equiv.Perm D) (d : D) : D → ℝ :=
  Pi.single d 1 - Pi.single (θ d) 1

omit [Fintype D] in
lemma edgeFlow_mem (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d) (d : D) :
    edgeFlow θ d ∈ antisymmetric θ := by
  intro e
  change (Pi.single d 1 : D → ℝ) (θ e) - (Pi.single (θ d) 1 : D → ℝ) (θ e) =
    -((Pi.single d 1 : D → ℝ) e - (Pi.single (θ d) 1 : D → ℝ) e)
  have he : θ e = d ↔ e = θ d := by
    constructor
    · intro h
      simpa only [hθ] using congrArg θ h
    · intro h
      rw [h,hθ]
  simp only [Pi.single_apply, he, Equiv.apply_eq_iff_eq, eq_comm]
  ring

omit [Fintype Z] in
lemma divergence_edgeFlow (b : D → Z) (θ : Equiv.Perm D) (d : D) :
    divergence b (edgeFlow θ d) = Pi.single (b d) 1 - Pi.single (b (θ d)) 1 := by
  rw [edgeFlow, map_sub, divergence_single, divergence_single]

/-- Adjacency in the graph dual to the band sides, with orientations retained. -/
def Adj (b : D → Z) (θ : Equiv.Perm D) (x y : Z) : Prop :=
  ∃ d, b d = x ∧ b (θ d) = y

omit [Fintype Z] in
lemma difference_mem_range (b : D → Z) (θ : Equiv.Perm D)
    (hθ : ∀ d, θ (θ d) = d) {x y : Z}
    (hxy : Relation.ReflTransGen (Adj b θ) x y) :
    Pi.single x 1 - Pi.single y 1 ∈
      LinearMap.range ((divergence b).comp (antisymmetric θ).subtype) := by
  induction hxy with
  | refl => simp
  | @tail y z hxy hyz ih =>
    obtain ⟨d,rfl,rfl⟩ := hyz
    have hd : Pi.single (b d) 1 - Pi.single (b (θ d)) 1 ∈
        LinearMap.range ((divergence b).comp (antisymmetric θ).subtype) := by
      refine ⟨⟨edgeFlow θ d, edgeFlow_mem θ hθ d⟩, ?_⟩
      exact divergence_edgeFlow b θ d
    convert (LinearMap.range ((divergence b).comp (antisymmetric θ).subtype)).add_mem ih hd using 1
    ext z
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

/-- Any total-zero boundary phases are
realized by antisymmetric phases on the paired slots of a connected diagram. -/
theorem exists_flow (b : D → Z) (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hconn : ∀ x y, Relation.ReflTransGen (Adj b θ) x y)
    (root : Z) (η : Z → ℝ) (hη : ∑ z, η z = 0) :
    ∃ γ : D → ℝ, (∀ d, γ (θ d) = -γ d) ∧
      ∀ z, (∑ d, if b d = z then γ d else 0) = η z := by
  let R := LinearMap.range ((divergence b).comp (antisymmetric θ).subtype)
  have he : η = ∑ z, η z • (Pi.single z 1 - Pi.single root 1) := by
    ext y
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hη, zero_mul, sub_zero]
    simp [Pi.single_apply]
  have hm : η ∈ R := by
    rw [he]
    apply Submodule.sum_mem
    intro z _
    exact R.smul_mem _ (difference_mem_range b θ hθ (hconn z root))
  obtain ⟨γ,hγ⟩ := hm
  refine ⟨γ,γ.property,?_⟩
  intro z
  exact congrFun hγ z
end

variable {D Z : Type*}
/-- Changing the disk successor to the boundary successor does not change
connectivity of the dual graph. -/
lemma dual_connected (b : D → Z) (hb : Function.Surjective b)
    (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hcycle : ∀ d, b (σ (θ d)) = b d)
    (hconn : ∀ d e, Relation.ReflTransGen (fun d e => e = σ d ∨ e = θ d) d e) :
    ∀ x y, Relation.ReflTransGen (Adj b θ) x y := by
  intro x y
  obtain ⟨d,rfl⟩ := hb x
  obtain ⟨e,rfl⟩ := hb y
  have hnext : ∀ a, b (σ a) = b (θ a) := by
    intro a
    simpa only [hθ] using hcycle (θ a)
  induction hconn d e with
  | refl => exact .refl
  | @tail a c h ha ih =>
    apply Relation.ReflTransGen.tail ih
    rcases ha with rfl | rfl
    · exact ⟨a,rfl,(hnext a).symm⟩
    · exact ⟨a,rfl,rfl⟩
end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
local instance : DecidableEq (Slot I K) := Classical.decEq _

def traversalSign (s : I → ℤ) : Slot I K → ℤ
  | (.inl _,i) => s i
  | (.inr _,i) => -s i

omit [Fintype I] [Fintype K] in
lemma traversalSign_positive (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (p : K × I) :
    traversalSign s (coordinates s (.inl p)) = 1 := by
  rcases p with ⟨k,i⟩
  rcases hs i with h | h <;> simp [coordinates,traversalSign,h]

omit [Fintype I] [Fintype K] in
lemma traversalSign_negative (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (p : K × I) :
    traversalSign s (coordinates s (.inr p)) = -1 := by
  rcases p with ⟨k,i⟩
  rcases hs i with h | h <;> simp [coordinates,traversalSign,h]

/-- The signed band involution supplies exactly the scalar hypotheses of the
full fixed-space mixing theorem. -/
lemma exists_band_mixer [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (γ : Slot I K → ℝ) (hγ : ∀ d, γ (θ d) = -γ d) :
    ∃ X : Matrix.unitaryGroup K ℂ, 2 * Fintype.card K ≤
      KervaireFixed.fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) *
        monomial θ (fun d ↦ scalarRotation (γ d))) := by
  let T := monomial θ (fun d ↦ scalarRotation (γ d))
  have hsT : star T = T := monomial_selfadjoint θ hθ _ (by
    intro d
    rw [hγ,star_scalarRotation])
  have huT : T ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ) :=
    monomial_unitary θ _ (fun d ↦ scalarRotation_unitary _)
  have h₀ (i j : K × I) : T (coordinates s (.inl i)) (coordinates s (.inl j)) = 0 := by
    have hn : coordinates s (.inl i) ≠ θ (coordinates s (.inl j)) := by
      intro he
      have hh := hop (coordinates s (.inl j))
      rw [← he,traversalSign_positive s hs,traversalSign_positive s hs] at hh
      omega
    simp only [T,monomial,ite_eq_right hn]
  have h₁ (i j : K × I) : T (coordinates s (.inr i)) (coordinates s (.inr j)) = 0 := by
    have hn : coordinates s (.inr i) ≠ θ (coordinates s (.inr j)) := by
      intro he
      have hh := hop (coordinates s (.inr j))
      rw [← he,traversalSign_negative s hs,traversalSign_negative s hs] at hh
      omega
    simp only [T,monomial,ite_eq_right hn]
  obtain ⟨X,hX⟩ := exists_mixer_for_exchange s hs hsum T hsT huT h₀ h₁
  exact ⟨X,hX⟩

lemma S_mul_bands (ρ : Equiv.Perm I) (a : I → A) (θ : Equiv.Perm (Slot I K)) (γ : Slot I K → ℝ) :
    S ρ a * scalarTensor (A := A) (monomial θ (fun d ↦ scalarRotation (γ d))) =
      weightedShift (successor ρ * θ) (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d)) := by
  rw [scalarTensor_monomial,S]
  have he : labelledShift (successor (K := K) ρ) (labels ρ a) =
      weightedShift (successor ρ) (fun _ ↦ 1) (labels ρ a) := by
    simp [weightedShift,scalarDiagonal_one]
  rw [he,weightedShift_mul]
  simp only [one_mul,mul_one]

/-- The literal phase bound for every antisymmetric real choice of band phases. -/
lemma boundary_phase_upper [Nonempty I] [Nonempty K] (ρ : Equiv.Perm I) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (γ : Slot I K → ℝ) (hγ : ∀ d, γ (θ d) = -γ d) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (successor ρ * θ)
      (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d)) (fun _ ↦ scalarRotation_unitary _))
    KervaireMatrix.phase (weightedShift (successor ρ * θ)
      (fun d ↦ scalarRotation (γ d)) (fun d ↦ labels ρ a (θ d))) ≤
        3/2 * (Fintype.card I : ℝ) * Fintype.card K - Fintype.card K := by
  obtain ⟨X,hX⟩ := exists_band_mixer s hs hsum θ hθ hop γ hγ
  have hTu := monomial_unitary θ (fun d ↦ scalarRotation (γ d)) (fun d ↦ scalarRotation_unitary _)
  have hTs := monomial_selfadjoint θ hθ (fun d ↦ scalarRotation (γ d)) (by
    intro d
    rw [hγ,star_scalarRotation])
  have hb := phase_upper_of_fixed ρ a _ hTu hTs X hX
  simpa only [S_mul_bands] using hb
end
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
variable {I K Z A : Type*} [Fintype I] [Fintype K] [Fintype Z] [Group A]
  [Nonempty I] [Nonempty K]
local instance : DecidableEq (Slot I K) := Classical.decEq _

theorem planar_boundary
    (ρ : Equiv.Perm I) (a : I → A) (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ Slot I K)
    (he : ∀ z i, ((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hconn : ∀ d f, Relation.ReflTransGen (fun d f => f = successor ρ d ∨ f = θ d) d f)
    (hEuler : Fintype.card Z + 2*Fintype.card K = 2+Fintype.card I*Fintype.card K)
    (z₀ : Z)
    (hc : ∀ z, z ≠ z₀ → orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1) :
    orbitWeight (finRotate (n z₀+1))
      (fun i ↦ labels ρ a (θ (e ⟨z₀,i⟩))) (n z₀+1) 0 = 1 := by
  let _ : Nonempty Z := ⟨z₀⟩
  let b : Slot I K → Z := fun d ↦ (e.symm d).1
  let c : Z → A := fun z ↦ orbitWeight (finRotate (n z+1))
    (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0
  have hb : Function.Surjective b := fun z ↦ ⟨e ⟨z,0⟩,by simp [b]⟩
  have hbcycle (d : Slot I K) : b (successor ρ (θ d)) = b d := by
    obtain ⟨⟨z,i⟩,rfl⟩ := e.surjective d
    change b (((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) (e ⟨z,i⟩)) = _
    rw [he]
    simp [b]
  have hbconn := KervaireFlow.dual_connected b hb (successor ρ) θ hθ hbcycle hconn
  apply trivial_of_boundary_inequalities z₀ c
  intro ε hε hε1
  let η : Z → ℝ := fun z ↦ (if z = z₀ then (Fintype.card Z : ℝ)*ε else 0) - ε
  have ηroot : η z₀ = ((Fintype.card Z : ℝ)-1)*ε := by simp only [η,ite_true,eq_self]; ring
  have ηother (z : Z) (hz : z ≠ z₀) : η z = -ε := by simp [η,hz]
  have hη : ∑ z, η z = 0 := by
    simp [η,Finset.sum_sub_distrib]
  obtain ⟨γ,hγ,hdiv⟩ := KervaireFlow.exists_flow b θ hθ hbconn z₀ η hη
  have hu := boundary_phase_upper ρ a s hs hsum θ hθ hop γ hγ
  have hphase := phase_boundary_cycles n e ((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) he γ
    (fun d ↦ labels ρ a (θ d)) η hdiv
  rw [hphase] at hu
  have hq : (Fintype.card Z : ℝ)+2*Fintype.card K = 2+(Fintype.card I : ℝ)*Fintype.card K := by
    exact_mod_cast hEuler
  have hsumphase : (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) ≤
      (Fintype.card Z : ℝ)-1 := by
    simp only [Slot,Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hu
    change _ + (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) ≤ _ at hu
    linarith
  have heq (z : Z) : groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z) =
      (1-ε) + if z = z₀ then groupPhase (scalarRotation (η z₀)) (scalarRotation_unitary _) (c z₀) - (1-ε) else 0 := by
    by_cases hz : z = z₀
    · subst z
      simp
    · have hcz : c z = 1 := hc z hz
      simp only [ite_eq_right hz,add_zero,hcz,ηother z hz,groupPhase_rotation_one hε hε1]
  have htotal : (∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _) (c z)) =
      groupPhase (scalarRotation (((Fintype.card Z : ℝ)-1)*ε)) (scalarRotation_unitary _) (c z₀)
        + ((Fintype.card Z : ℝ)-1)*(1-ε) := by
    rw [Finset.sum_congr rfl (fun z _ ↦ heq z)]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,ηroot]
    ring
  rwa [htotal] at hsumphase
end KervaireBoundary

end

end OAI
