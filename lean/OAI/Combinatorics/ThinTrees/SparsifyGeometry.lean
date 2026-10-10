import OAI.Combinatorics.ThinTrees.StepBounds

namespace OAI

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_dot (B : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian B) v=∑e ∈ B, (v ⬝ᵥ G.incidence e)^2 :=
  qform_covariance G.incidence B v

lemma sparsify_from_extraction (hn : 2 ≤ n) {r : ℕ} (hnum : StepNumeric r)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain)
    (hp : G.TreePackable (G.thresholdEdges (G.resistance X) (4*resistanceT r)) (extractQ r)) :
    ∃A : Finset (Fin m), G.TreePackable A (stepCount r) ∧
      ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
        ((G.cut A S).card:ℝ) ≤ (1/2+3*splitTau r)*(G.cut univ S).card := by
  classical
  have hrp : 0 < r := by have := hnum.rlarge; omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hrp
  have hu : 0 < errorU r := Real.rpow_pos_of_pos hrR _
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hε : 0 < splitEpsilon r := by unfold splitEpsilon; positivity
  have hτ0 : 0 ≤ splitTau r := by unfold splitTau; positivity
  have hc : 0 < 1/2-splitTau r := by have := hnum.usmall; have := hnum.tausmall; linarith
  obtain ⟨F,hF,hd⟩ := hp
  let B := univ.biUnion F
  have hB : B ⊆ G.thresholdEdges (G.resistance X) (4*resistanceT r) := by
    intro e he
    obtain ⟨i,_,hei⟩ := mem_biUnion.mp he
    exact (hF i).1 hei
  obtain ⟨L,s,hs,hiso,hnorm⟩ := G.graph_isotropic_representation hnum.qpos hn F (fun i => (hF i).2) hd hu
  let z : Fin m → Fin (n-1) → ℝ := fun e => s e • L ⟨G.incidence e,G.incidence_zeroSum e⟩
  change (∑e ∈ B, vecMulVec (z e) (z e))=1 at hiso
  change ∀e ∈ B, z e ⬝ᵥ z e ≤ (1+errorU r)/(extractQ r:ℝ) at hnorm
  obtain ⟨a,ha,haNorm,haTest⟩ := G.normalized_vectors (by omega) hX B
  have hsum {V : Type} [AddCommMonoid V] (f : Fin m → V) :
      (∑e : B, f e)=∑e ∈ B, f e := by
    simpa only [attach_eq_univ] using sum_attach B f
  have hnormB (e : B) : a e ⬝ᵥ a e+z e ⬝ᵥ z e ≤ splitEpsilon r := by
    have hh := (mem_filter.mp (hB e.property)).2
    have hz := (hnorm e e.property).trans hnum.size
    rw [haNorm]
    unfold splitEpsilon
    linarith
  have haB (x : Fin n → ℝ) : (∑e : B, (x ⬝ᵥ a e)^2) ≤ x ⬝ᵥ x := by
    rw [hsum (fun e => (x ⬝ᵥ a e)^2)]; exact ha x
  have hzB (y : Fin (n-1) → ℝ) : (∑e : B, (y ⬝ᵥ z e)^2)=y ⬝ᵥ y := by
    rw [hsum (fun e => (y ⬝ᵥ z e)^2),←qform_covariance,hiso,qform,one_mulVec]
  obtain ⟨A₀,hAhi,hAlo⟩ := split_two_systems (fun e : B => a e) (fun e : B => z e) hε haB hzB hnormB
  let A : Finset (Fin m) := A₀.image Subtype.val
  have hAB : A ⊆ B := by
    intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact i.property
  have hsumA {V : Type} [AddCommMonoid V] (f : Fin m → V) :
      (∑e ∈ A, f e)=∑e ∈ A₀, f e := by
    exact sum_image (fun _ _ _ _ h => Subtype.ext h)
  have hlow : ((∑e ∈ A, vecMulVec (z e) (z e))-
      (1/2-splitTau r) • (1 : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.posSemidef_sum A (fun e _ => by
        simpa only [star_trivial] using posSemidef_vecMulVec_self_star (z e))).isHermitian.sub
        (Matrix.PosSemidef.one.smul hc.le).isHermitian)
    intro y
    have hh := hAlo y
    change (1/2-splitTau r)*(y ⬝ᵥ y) ≤ ∑e ∈ A₀, (y ⬝ᵥ z e)^2 at hh
    rw [←hsumA (fun e => (y ⬝ᵥ z e)^2)] at hh
    change 0 ≤ qform _ y
    rw [qform_sub,qform_covariance,qform_smul,qform,one_mulVec]
    linarith
  have hpack := G.projected_trace_treePackable hn hnum.qpos hu hc L s hs A B hAB hnorm hlow
  refine ⟨A,G.treePackable_mono_count hnum.packing hpack,?_⟩
  intro S hS hS'
  obtain ⟨x,hx,he⟩ := haTest (cutIndicator S)
  have hh := hAhi x
  change (∑e ∈ A₀, (x ⬝ᵥ a e)^2) ≤
    (1/2:ℝ)*(∑e : B, (x ⬝ᵥ a e)^2)+splitTau r*(x ⬝ᵥ x) at hh
  rw [←hsumA (fun e => (x ⬝ᵥ a e)^2),hsum (fun e => (x ⬝ᵥ a e)^2),hx] at hh
  simp_rw [he] at hh
  rw [←G.laplacian_dot,←G.laplacian_dot,G.laplacian_cut,G.laplacian_cut] at hh
  have hcutSub : G.cut B S ⊆ G.cut univ S := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
  have hcut : ((G.cut B S).card:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast card_le_card hcutSub
  have hXcut := mul_le_mul_of_nonneg_left (hX.2 S hS hS') hτ0
  nlinarith

end StrongThinTree.MultiGraph

end
end

end OAI
