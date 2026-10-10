import OAI.NumberTheory.ShortEgyptian.ResidueSystem

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma isUnitSum_of_positive {x : ℚ} {ns : List ℕ}
    (hp : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = x) (hx : x < 1) : IsUnitSum x ns := by
  refine ⟨?_,heq⟩
  intro n hn
  have hh := unit_le_sum hn
  rw [heq] at hh
  have hn0 := hp n hn
  by_contra h
  have hn1 : n = 1 := by omega
  subst n
  norm_num at hh
  linarith

lemma binary_unitSum (a M u : ℕ) (hM : 0 < M) (hd : 2^a ∣ M) (hu : u ≤ 2^a) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ unitSum ns = (u:ℚ)/M ∧ ns.length ≤ a+1 := by
  induction a generalizing u with
  | zero =>
    have hu' : u = 0 ∨ u = 1 := by norm_num at hu; omega
    rcases hu' with rfl | rfl
    · exact ⟨[],by simp,by simp,by simp⟩
    · exact ⟨[M],by simpa using hM,by simp,by simp⟩
  | succ a ih =>
    have hd' : 2^a ∣ M := (pow_dvd_pow 2 (by omega : a ≤ a+1)).trans hd
    by_cases hsmall : u ≤ 2^a
    · obtain ⟨ns,hns,heq,hlen⟩ := ih u hd' hsmall
      exact ⟨ns,hns,heq,by omega⟩
    · have hpow : 0 < 2^a := by positivity
      have hdpos : 0 < M/2^a := Nat.div_pos (Nat.le_of_dvd hM hd') hpow
      have hur : u-2^a ≤ 2^a := by rw [pow_succ] at hu; omega
      obtain ⟨ns,hns,heq,hlen⟩ := ih (u-2^a) hd' hur
      refine ⟨(M/2^a)::ns,by simpa using And.intro hdpos hns,?_,by simpa using Nat.succ_le_succ hlen⟩
      rw [unitSum_cons,heq]
      have hdiv : ((M/2^a:ℕ):ℚ)*(2:ℚ)^a = M := by exact_mod_cast Nat.div_mul_cancel hd'
      have huQ : (u:ℚ) = (u-2^a:ℕ)+(2:ℚ)^a := by exact_mod_cast (Nat.sub_add_cancel (by omega : 2^a ≤ u)).symm
      have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
      have hdq : ((M/2^a:ℕ):ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
      field_simp
      nlinarith

lemma residue_lift {M Q Q' u t k : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hQ' : 0 < Q')
    (hQQ : Q' ∣ Q) (hu : 0 < u) (huM : u < M*Q) (ht : 0 < t) (htM : t ∣ M)
    (hr : ∃ ns, IsUnitSum ((residue (Q*t) u (quotient (Q*t) u):ℚ)/(M*Q')) ns ∧ ns.length ≤ k) :
    ∃ ns, IsUnitSum ((u:ℚ)/(M*Q)) ns ∧ ns.length ≤ k+1 := by
  let z := quotient (Q*t) u
  let r := residue (Q*t) u z
  have hz : 0 < z := (quotient_spec (Nat.mul_pos hQ ht) hu).1
  have hdt : 0 < M/t := Nat.div_pos (Nat.le_of_dvd hM htM) ht
  have hdQ : 0 < Q/Q' := Nat.div_pos (Nat.le_of_dvd hQ hQQ) hQ'
  let g := z*(Q/Q')
  have hg : 0 < g := Nat.mul_pos hz hdQ
  obtain ⟨ns,hns,hlen⟩ := hr
  let ns' := (M/t*z)::ns.map (g*·)
  have hpos : ∀ n ∈ ns', 0 < n := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact Nat.mul_pos hdt hz
    · obtain ⟨n,hnn,rfl⟩ := List.mem_map.mp hn
      exact Nat.mul_pos hg (by have hh := hns.1 n hnn; omega)
  have heq : unitSum ns' = (u:ℚ)/(M*Q) := by
    dsimp only [ns']
    rw [unitSum_cons,unitSum_scale,hns.2,residue_identity hM hQ hu ht htM]
    push_cast
    congr 1
    have hh : (Q/Q':ℕ)*Q'=Q := Nat.div_mul_cancel hQQ
    have hhq : ((Q/Q':ℕ):ℚ)*Q'=Q := by exact_mod_cast hh
    have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hQq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hQ'q : (Q':ℚ) ≠ 0 := by exact_mod_cast hQ'.ne'
    have hzq : (z:ℚ) ≠ 0 := by exact_mod_cast hz.ne'
    have hdq : ((Q/Q':ℕ):ℚ) ≠ 0 := by exact_mod_cast hdQ.ne'
    change (r:ℚ)/(M*Q') / (g:ℚ) = (r:ℚ)/(M*Q*z)
    rw [show (g:ℚ) = (z:ℚ)*(Q/Q':ℕ) from Nat.cast_mul _ _]
    field_simp
    nlinarith
  refine ⟨ns',isUnitSum_of_positive hpos heq ?_,by simpa [ns'] using Nat.succ_le_succ hlen⟩
  apply (div_lt_one (by positivity : (0:ℚ)<M*Q)).mpr
  exact_mod_cast huM

end ShortEgyptian

end OAI
