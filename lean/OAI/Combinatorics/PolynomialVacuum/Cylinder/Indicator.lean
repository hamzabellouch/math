import OAI.Combinatorics.PolynomialVacuum.Cylinder.Contour

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}
noncomputable def flowRadius (q : Edge M →₀ ℤ) : ℕ :=
  q.support.sup fun e => e.1.2.natAbs

theorem flow_support_height (q : Edge M →₀ ℤ) (e : Edge M) (he : e∈q.support) :
    -(flowRadius q : ℤ) ≤ e.1.2 ∧ e.1.2 ≤ flowRadius q := by
  have h : e.1.2.natAbs ≤ flowRadius q := Finset.le_sup (f:=fun e : Edge M => e.1.2.natAbs) he
  have hi : |e.1.2| ≤ (flowRadius q : ℤ) := by
    simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h
  exact abs_le.mp hi

theorem finitePrefix_eq_zero (f : ℤ →₀ ℤ) (j : ℤ)
    (h : ∀ k∈f.support, j≤k) : finitePrefix j f=0 := by
  classical
  simp only [finitePrefix,Finsupp.liftAddHom_apply,Finsupp.sum]
  apply Finset.sum_eq_zero
  intro k hk
  simp [not_lt.mpr (h k hk)]

theorem potential_bottom_zero (q : Edge M →₀ ℤ) (i : ZMod M) (j : ℤ)
    (hj : j ≤ -(flowRadius q : ℤ)) : potential q (i,j)=0 := by
  dsimp [potential]
  rw [finitePrefix_eq_zero]
  · rfl
  · intro k hk
    have he : ((i+1,k),2)∈q.support := by
      simpa only [Finsupp.mem_support_iff,column_apply] using hk
    exact hj.trans (flow_support_height q _ he).1

theorem bottom_potential_two_values (p : Face M → ℤ) (A B m : ℤ)
    (hbottom : ∀ i j, j ≤ m → p (i,j)=0) (hp : p ≠ 0)
    (hgrad : ∀ i j, p (i,j)-p (i,j+1) ≠ 0 →
      (p (i,j)=A ∨ p (i,j)=B) ∧ (p (i,j+1)=A ∨ p (i,j+1)=B)) :
    (A=0 ∨ B=0) ∧ ∀ a : Face M, p a=A ∨ p a=B := by
  have hz : A=0 ∨ B=0 := by
    by_contra hn
    push Not at hn
    apply hp
    funext a
    rcases a with ⟨i,j⟩
    change p (i,j)=0
    by_cases hj : j ≤ m
    · exact hbottom i j hj
    · apply Int.leInduction (motive:=fun k _ => p (i,k)=0) (hbottom i m le_rfl) ?_ j (by omega)
      intro k hk hpk
      by_cases he : p (i,k+1)=p (i,k)
      · exact he.trans hpk
      · have h := (hgrad i k (by omega)).1
        rw [hpk] at h
        exact False.elim (h.elim (fun h => hn.1 h.symm) (fun h => hn.2 h.symm))
  refine ⟨hz,?_⟩
  rintro ⟨i,j⟩
  have hb : p (i,m)=A ∨ p (i,m)=B := by
    rw [hbottom i m le_rfl]
    exact hz.imp Eq.symm Eq.symm
  by_cases hj : j ≤ m
  · rw [hbottom i j hj]
    exact hz.imp Eq.symm Eq.symm
  · apply Int.leInduction (motive:=fun k _ => p (i,k)=A ∨ p (i,k)=B) hb ?_ j (by omega)
    intro k hk hpk
    by_cases he : p (i,k+1)=p (i,k)
    · simpa only [he] using hpk
    · exact (hgrad i k (by omega)).2

 

theorem simple_closed_word_indicator (g : Germ M) (w : List Bool) (hne : w≠[])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w=g) :
    ∃ ε : ℤ, (ε=1 ∨ ε = -1) ∧
      ∀ a : Face M, potential (wordFlow g w) a=0 ∨ potential (wordFlow g w) a=ε := by
  let p := potential (wordFlow g w)
  have hp : RepresentsFlow p (wordFlow g w) := closed_word_has_potential g w hc
  have hw := simple_closed_word_contour g w hN hc
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs := localContour_sides p (wordFlow g (b::u)) hp g b hw.1
  let A := p (rightFace g)
  let B := p (leftFace g)
  have hAB : A-B=1 := hs.2.2
  have hpne : p ≠ 0 := by intro hz; simp only [A,B,hz,Pi.zero_apply,sub_zero] at hAB; omega
  have ht : (A=0 ∨ B=0) ∧ ∀ a : Face M, p a=A ∨ p a=B := by
    apply bottom_potential_two_values p A B (-(flowRadius (wordFlow g (b::u)) : ℤ))
      (potential_bottom_zero _) hpne
    intro i j hij
    have hgrad := (potential_gradient (wordFlow g (b::u)) (closed_word_conserved g _ hc) (i+1) j).2.2
    simp only [add_sub_cancel_right] at hgrad
    have hq : wordFlow g (b::u) ((i+1,j),2) ≠ 0 := by simpa only [hgrad] using hij
    have h := wordFlow_edge_sides p _ hp g (b::u) hw ((i+1,j),2) hq
    simpa [SideValues,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor,A,B] using h
  rcases ht.1 with hA | hB
  · have hBm : B = -1 := by omega
    refine ⟨-1,Or.inr rfl,?_⟩
    intro a; simpa only [hA,hBm] using ht.2 a
  · have hAp : A=1 := by omega
    refine ⟨1,Or.inl rfl,?_⟩
    intro a; simpa only [hAp,hB,or_comm] using ht.2 a
end PolynomialVacuumCylinder

end OAI
