import Mathlib
import OAI.Geometry.HyperbolicGroups.GeneralSwitch
import OAI.Geometry.HyperbolicGroups.MappedPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I L V : Type*}
namespace PictureMap

/-- Two oppositely oriented face boundaries, including their particular
cyclic parametrizations. The two occurrences are disjoint, even if the target
cell or some target boundary vertices coincide. -/
structure OppositeFaces (f : Perm D) (q : Perm I) (a b : I → D) : Prop where
  a_inj : Function.Injective a
  b_inj : Function.Injective b
  disjoint : ∀ i j, a i ≠ b j
  a_face : ∀ i, f (a i) = a (q i)
  b_face : ∀ i, f (b (q i)) = b i
  cyclic : ∀ i j, q.SameCycle i j

variable (M : PictureMap D) {q : Perm I} {a b : I → D}

lemma paired_reverse {i : I} (h : M.edge (a i) = b i) : M.edge (b i) = a i := by
  rw [← h,M.edge_edge]

lemma dipole_sameVertex (hF : OppositeFaces M.face q a b) {i : I}
    (hp : M.edge (a i) = b i) :
    M.vertex.SameCycle (a (q i)) (M.edge (b (q i))) := by
  have hy : M.vertex (M.edge (b (q i))) = b i := by
    change M.face (M.edge (M.edge (b (q i)))) = b i
    rw [M.edge_edge,hF.b_face]
  have hx : M.vertex (b i) = a (q i) := by
    change M.face (M.edge (b i)) = a (q i)
    rw [M.paired_reverse hp,hF.a_face]
  have hh : M.vertex.SameCycle (M.edge (b (q i)))
      (M.vertex (M.vertex (M.edge (b (q i))))) := SameCycle.rfl.apply_right.apply_right
  rw [hy,hx] at hh
  exact hh.symm

variable [DecidableEq D]

/-- The elementary cancellation switch pairs the next two boundary sides,
while retaining every already paired side of the two cancellation faces. -/
lemma dipole_switch_pairs (hF : OppositeFaces M.face q a b) (k : I) :
    (M.switch (a k) (M.edge (b k))).edge (a k) = b k ∧
      ∀ j, M.edge (a j) = b j → (M.switch (a k) (M.edge (b k))).edge (a j) = b j := by
  have hnew : (M.switch (a k) (M.edge (b k))).edge (a k) = b k := by
    rw [M.switch_edge_a_of_ne]
    · exact M.edge_edge (b k)
    · rw [M.edge_edge]
      exact (hF.disjoint k k).symm
  refine ⟨hnew,?_⟩
  intro j hj
  by_cases he : j = k
  · simpa only [he] using hnew
  have h₁ : a j ≠ a k := hF.a_inj.ne he
  have h₂ : a j ≠ M.edge (b k) := by
    intro h
    have hh := congrArg M.edge h
    rw [M.edge_edge,hj] at hh
    exact he (hF.b_inj hh)
  have h₃ : b j ≠ a k := (hF.disjoint k j).symm
  have h₄ : b j ≠ M.edge (b k) := by
    intro h
    have hh := congrArg M.edge h
    rw [M.edge_edge,M.paired_reverse hj] at hh
    exact hF.disjoint j k hh
  change swap (a k) (M.edge (b k)) (M.edge (swap (a k) (M.edge (b k)) (a j))) = b j
  rw [swap_apply_of_ne_of_ne h₁ h₂,hj,swap_apply_of_ne_of_ne h₃ h₄]

variable [Fintype D] [Fintype I]

/-- A complete dipole can be separated by finitely many genuine crosswise
side-pairing switches. This is the producer behind cancellation in a minimal
mapped sphere/disk picture. It preserves genus zero, the face permutation and
all original oriented side labels; it does NOT presuppose a normal picture. -/
theorem isolate_dipole (hF : OppositeFaces M.face q a b) (i₀ : I)
    (hseed : M.edge (a i₀) = b i₀) {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hG : M.GenusZero)
    (hinv : ∀ l, rev (rev l) = l) (hop : ∀ i, label (b i) = rev (label (a i))) :
    ∃ N : PictureMap D, N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero ∧
      (∀ i, M.edge (a i) = b i → N.edge (a i) = b i) ∧ ∀ i, N.edge (a i) = b i := by
  classical
  let good : PictureMap D → Prop := fun N => N.face = M.face ∧ N.Respects label start rev ∧
    N.GenusZero ∧ ∀ i, M.edge (a i) = b i → N.edge (a i) = b i
  let paired : PictureMap D → Finset I := fun N => Finset.univ.filter (fun i => N.edge (a i) = b i)
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨rfl,hM,hG,fun _ h => h⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => (paired N).card) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  have fn : OppositeFaces N.face q a b := by rw [hn.1]; exact hF
  have hadvance : ∀ i, N.edge (a i) = b i → N.edge (a (q i)) = b (q i) := by
    intro i hi
    by_contra hbad
    let T := N.switch (a (q i)) (N.edge (b (q i)))
    have hl : label (a (q i)) = label (N.edge (b (q i))) := by
      rw [hn.2.1.2,hop,hinv]
    have ht : good T := ⟨hn.1,switch_respects hn.2.1 hl,
      N.switch_genusZero_general hn.2.2.1 _ _ (N.dipole_sameVertex fn hi),
      fun j hj => (N.dipole_switch_pairs fn (q i)).2 j (hn.2.2.2 j hj)⟩
    have hsub : paired N ⊆ paired T := by
      intro j hj
      have hj' : N.edge (a j) = b j := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.dipole_switch_pairs fn (q i)).2 j hj'⟩
    have hnew : q i ∈ paired T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.dipole_switch_pairs fn (q i)).1⟩
    have hold : q i ∉ paired N := by simpa only [paired,Finset.mem_filter,Finset.mem_univ,true_and] using hbad
    have hstrict : paired N ⊂ paired T := lt_of_le_of_ne hsub (fun he => hold (he ▸ hnew))
    have hlt := Finset.card_lt_card hstrict
    have hmem : T ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
    have hle := hmax T hmem
    omega
  refine ⟨N,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,?_⟩
  intro i
  obtain ⟨n,rfl⟩ := (hF.cyclic i₀ i).exists_nat_pow_eq
  induction n with
  | zero => simpa only [pow_zero,one_apply] using hn.2.2.2 i₀ hseed
  | succ n ih =>
      rw [pow_succ',mul_apply]
      exact hadvance _ ih

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
