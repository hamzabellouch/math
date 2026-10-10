import Mathlib

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.AngularPartition

theorem exists_continuousOn_gluing {ι : Type*} [Finite ι]
    (s : ι → Set ℝ) (g : ι → ℝ → ℝ)
    (hs : ∀ i, IsClosed (s i)) (hg : ∀ i, ContinuousOn (g i) (s i))
    (hagree : ∀ i j x, x ∈ s i → x ∈ s j → g i x = g j x) :
    ∃ f : ℝ → ℝ, ContinuousOn f (⋃ i, s i) ∧ ∀ i, EqOn f (g i) (s i) := by
  classical
  let f : ℝ → ℝ := fun x => if h : ∃ i, x ∈ s i then g h.choose x else 0
  have hf : ∀ i, EqOn f (g i) (s i) := by
    intro i x hx
    dsimp [f]
    rw [dite_eq_left (show ∃ index, x ∈ s index from ⟨i,hx⟩)]
    exact hagree _ i x (Exists.choose_spec (show ∃ j, x ∈ s j from ⟨i,hx⟩)) hx
  refine ⟨f,?_,hf⟩
  exact (locallyFinite_of_finite s).continuousOn_iUnion hs
    (fun i => (hg i).congr (hf i))

theorem node_strictMonoOn {N : ℕ} (node : ℕ → ℝ)
    (hstep : ∀ j < N, node j < node (j+1)) :
    StrictMonoOn node (Iic N) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact hstep j hj

theorem exists_cell {N : ℕ} (hN : 0 < N) (node : ℕ → ℝ)
    {x : ℝ} (hx0 : node 0 ≤ x) (hxN : x ≤ node N) :
    ∃ j : Fin N, x ∈ Icc (node j) (node (j+1)) := by
  have hex : ∃ i : ℕ, 0 < i ∧ i ≤ N ∧ x ≤ node i := ⟨N,hN,le_rfl,hxN⟩
  let k := Nat.find hex
  have hk : 0 < k ∧ k ≤ N ∧ x ≤ node k := Nat.find_spec hex
  have hkm : k - 1 + 1 = k := by omega
  refine ⟨⟨k-1,by omega⟩,?_,by simpa only [hkm] using hk.2.2⟩
  by_cases h : k = 1
  · simpa only [h, Nat.sub_self] using hx0
  · have hmin := Nat.find_min hex (show k-1 < Nat.find hex by dsimp [k] at *; omega)
    by_contra! hbad
    exact hmin ⟨by omega,by omega,hbad.le⟩

theorem affine_agree_on_overlap {N : ℕ} (node α β : ℕ → ℝ)
    (hstep : ∀ j < N, node j < node (j+1))
    (hmatch : ∀ j, j+1 < N →
      α j-node (j+1)*β j = α (j+1)-node (j+1)*β (j+1)) :
    ∀ i j : Fin N, ∀ x : ℝ,
      x ∈ Icc (node i) (node (i+1)) → x ∈ Icc (node j) (node (j+1)) →
      α i-x*β i = α j-x*β j := by
  have hm := (node_strictMonoOn node hstep)
  have hordered : ∀ i j : Fin N, i < j → ∀ x : ℝ,
      x ∈ Icc (node i) (node (i+1)) → x ∈ Icc (node j) (node (j+1)) →
      α i-x*β i = α j-x*β j := by
    intro i j hij x hxi hxj
    have hijv : (i : ℕ) < j := hij
    have hn : node (i+1) ≤ node j := hm.monotoneOn (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)
    have hx : x = node (i+1) := le_antisymm hxi.2 (hn.trans hxj.1)
    have heq : (i : ℕ)+1 = j := by
      by_contra hne
      have hlt : (i : ℕ)+1 < j := by omega
      have hnodes := hm (by simp only [mem_Iic]; omega) (by simp only [mem_Iic]; omega) hlt
      linarith [hxj.1]
    rw [hx]
    have h := hmatch i (by omega)
    simpa only [heq] using h
  intro i j x hxi hxj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hordered i j hij x hxi hxj
  · subst j; rfl
  · exact (hordered j i hij x hxj hxi).symm

theorem exists_compatible_boundary {N : ℕ} (hN : 0 < N) (node α β : ℕ → ℝ)
    (hstep : ∀ j < N, node j < node (j+1))
    (hmatch : ∀ j, j+1 < N →
      α j-node (j+1)*β j = α (j+1)-node (j+1)*β (j+1)) :
    ∃ L : ℝ → ℝ, ContinuousOn L (Icc (node 0) (node N)) ∧
      ∀ j < N, ∀ x ∈ Icc (node j) (node (j+1)), L x = α j-x*β j := by
  obtain ⟨L,hL,heq⟩ := exists_continuousOn_gluing
    (fun j : Fin N => Icc (node j) (node (j+1)))
    (fun j : Fin N => fun x : ℝ => α j-x*β j)
    (fun _ => isClosed_Icc) (fun _ => by fun_prop)
    (affine_agree_on_overlap node α β hstep hmatch)
  refine ⟨L,hL.mono ?_,?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := exists_cell hN node hx.1 hx.2
    exact mem_iUnion.mpr ⟨j,hj⟩
  · intro j hj x hx
    exact heq ⟨j,hj⟩ hx

theorem exists_compatible_boundary_endpoints {N : ℕ} (hN : 0 < N)
    (node α β : ℕ → ℝ) (hzero : node 0 = -1) (hlast : node N = 1)
    (hstep : ∀ j < N, node j < node (j+1))
    (hmatch : ∀ j, j+1 < N →
      α j-node (j+1)*β j = α (j+1)-node (j+1)*β (j+1))
    (hleft : α 0 + β 0 = 0) (hright : α (N-1)-β (N-1) = 0) :
    ∃ L : ℝ → ℝ, ContinuousOn L (Icc (-1:ℝ) 1) ∧ L (-1) = 0 ∧ L 1 = 0 ∧
      ∀ j < N, ∀ x ∈ Icc (node j) (node (j+1)), α j-x*β j = L x := by
  obtain ⟨L,hL,heq⟩ := exists_compatible_boundary hN node α β hstep hmatch
  have hm : N-1+1=N := by omega
  refine ⟨L,by simpa only [hzero,hlast] using hL,?_,?_,?_⟩
  · have h := heq 0 hN (node 0) ⟨le_rfl,(hstep 0 hN).le⟩
    simpa only [hzero,neg_one_mul,sub_neg_eq_add,hleft] using h
  · have h := heq (N-1) (by omega) (node N)
      ⟨by simpa only [hm] using (hstep (N-1) (by omega)).le,by simp only [hm, le_refl]⟩
    simpa only [hlast,one_mul,hright] using h
  · intro j hj x hx
    exact (heq j hj x hx).symm

end CylinderCovering.AngularPartition

end

end OAI
