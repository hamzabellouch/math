import OAI.Combinatorics.MatchingEntropy.EntropyUpper

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_entropy_main (G : LooplessGraph V E)
    (_hn : 2 ≤ Fintype.card V) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    separableLower x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ binaryEntropy x :=
  ⟨separable_lower G hPM x hx, maxMatchingEntropy_le_binary G x hx⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in

theorem selected_uniform_mean (G : LooplessGraph V E) {k : ℕ} (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (M i).val (M j).val) :
    ∃ x ∈ G.polytope, ∀ e, x e=0 ∨ x e=1/(k:ℝ) := by
  classical
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsum : (∑ i : Fin k, (1/(k:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  let x := ∑ i : Fin k, (1/(k:ℝ)) • G.indicator (M i)
  refine ⟨x,?_,?_⟩
  · exact (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
      (fun (i : Fin k) _ => (one_div_pos.mpr hkR).le) hsum
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self (M i)))
  · intro e
    dsimp only [x]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    by_cases he : ∃ i, e ∈ (M i).val
    · obtain ⟨i,hi⟩ := he
      right
      rw [Finset.sum_eq_single i]
      · simp [LooplessGraph.indicator,hi]
      · intro j _ hji
        have hj : e ∉ (M j).val := fun h =>
          Finset.disjoint_left.mp (hdisjoint j i hji) h hi
        simp [LooplessGraph.indicator,hj]
      · simp
    · left
      apply Finset.sum_eq_zero
      intro i _
      have hi : e ∉ (M i).val := fun h => he ⟨i,h⟩
      simp [LooplessGraph.indicator,hi]

theorem separableLower_uniform (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 2 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (huniform : ∀ e, x e=0 ∨ x e=1/(k:ℝ)) :
    separableLower x = (r:ℝ)*(Real.log (k:ℝ)+
      (3*((k-1:ℕ):ℝ))*Real.log (1-1/(k:ℝ))) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkcast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have ha (e : E) : Real.negMulLog (x e)=x e*Real.log (k:ℝ) := by
    rcases huniform e with he | he
    · simp [he]
    · rw [he,one_div,Real.negMulLog,Real.log_inv]
      ring
  have hb (e : E) : Real.negMulLog (1-x e)=
      -((k:ℝ)-1)*x e*Real.log (1-1/(k:ℝ)) := by
    rcases huniform e with he | he
    · simp [he]
    · rw [he,Real.negMulLog]
      field_simp
  unfold separableLower entropy
  simp_rw [ha,hb]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,G.marginal_sum hV hx,hkcast]
  ring

theorem structuralBase_eq_exp {k : ℕ} (hk : 2 ≤ k) :
    structuralBase k = Real.exp (Real.log (k:ℝ)+
      (3*((k-1:ℕ):ℝ))*Real.log (1-1/(k:ℝ))) := by
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have ht : 0<1-1/(k:ℝ) := by
    have hh := (div_lt_one (by linarith : (0:ℝ)<k)).mpr hkR
    linarith
  rw [structuralBase,ite_eq_right (by omega),Real.exp_add,Real.exp_log (by linarith)]
  have hc : (3*((k-1:ℕ):ℝ)) = ((3*(k-1):ℕ):ℝ) := by push_cast; ring
  rw [hc,Real.exp_nat_mul,Real.exp_log ht]

theorem structuralBase_lower {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (-3)*(k:ℝ) ≤ structuralBase k := by
  by_cases hk1 : k=1
  · subst k
    simp only [structuralBase,ite_true,Nat.cast_one,mul_one]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  · have hk2 : 2 ≤ k := by omega
    have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
    have hk0 : (0:ℝ)<k := by linarith
    have ht : 0<1-1/(k:ℝ) := sub_pos.mpr ((div_lt_one hk0).mpr hkR)
    have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    rw [Real.log_inv] at hb
    have hkm : 0<(k:ℝ)-1 := by linarith
    have heq : ((1-1/(k:ℝ))⁻¹-1)*((k:ℝ)-1)=1 := by
      field_simp
      ring
    have hh := mul_le_mul_of_nonneg_right hb hkm.le
    rw [heq] at hh
    have hlog : -1 ≤ ((k:ℝ)-1)*Real.log (1-1/(k:ℝ)) := by nlinarith
    rw [structuralBase_eq_exp hk2]
    have hkcast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hbase : Real.exp (-3)*(k:ℝ)=Real.exp (-3+Real.log (k:ℝ)) := by
      rw [Real.exp_add,Real.exp_log hk0]
    rw [hbase]
    apply Real.exp_le_exp.mpr
    rw [hkcast]
    nlinarith

theorem uniform_support_count (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 1 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (huniform : ∀ e, x e=0 ∨ x e=1/(k:ℝ)) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  have hPM : Nonempty G.Matching := by
    obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
    by_contra h
    have : IsEmpty G.Matching := not_nonempty_iff.mp h
    simpa using hp.1.2
  have hN : (0:ℝ)<Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  constructor
  · by_cases hk1 : k=1
    · subst k
      simp only [structuralBase,ite_true,one_pow]
      exact_mod_cast (Fintype.card_pos_iff.mpr hPM)
    · have hk2 : 2 ≤ k := by omega
      have hlog := (separable_lower G hPM x hx).trans (maxMatchingEntropy_le_log_card G hx)
      rw [separableLower_uniform G hV hk2 hx huniform] at hlog
      have he := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hN,Real.exp_nat_mul,← structuralBase_eq_exp hk2] at he
      exact he
  · exact pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
      (structuralBase_lower hk) r

theorem structural_count_main (G : LooplessGraph V E) (r k : ℕ)
    (_hr : 0<r) (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hdisjoint : ∀ i j, i≠j → Disjoint (M i).val (M j).val) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  obtain ⟨x,hx,hu⟩ := selected_uniform_mean G hk M hdisjoint
  exact uniform_support_count G hV hk hx hu

theorem regular_uniform_mem (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card=k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    (fun _ : E => 1/(k:ℝ)) ∈ G.polytope := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  rw [G.polytope_eq_constraints (by rw [hV]; exact even_two_mul r)]
  refine ⟨fun _ => (one_div_pos.mpr hkR).le,?_,?_⟩
  · intro v
    unfold LooplessGraph.degree
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,hregular]
    field_simp
  · intro S hS
    unfold LooplessGraph.cutMass
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hc : (k:ℝ) ≤ (G.cut S).card := by exact_mod_cast hodd S hS
    calc
      1 = (k:ℝ)*(1/(k:ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (one_div_pos.mpr hkR).le

theorem regular_count_main (G : LooplessGraph V E) (r k : ℕ)
    (_hr : 0<r) (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card=k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  exact uniform_support_count G hV hk (regular_uniform_mem G hV hk hregular hodd)
    (fun _ => Or.inr rfl)

end MatchingEntropyBounds

end

end OAI
