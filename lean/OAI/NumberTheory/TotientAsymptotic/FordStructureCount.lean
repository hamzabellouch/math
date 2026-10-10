import OAI.NumberTheory.TotientAsymptotic.FirstFailedRows
import OAI.NumberTheory.TotientAsymptotic.TopRowCount
import OAI.NumberTheory.TotientAsymptotic.SmallTerminalTail
import OAI.NumberTheory.TotientAsymptotic.BootstrapLargeValues
import OAI.NumberTheory.TotientAsymptotic.SecondPrimeBound
import OAI.NumberTheory.TotientAsymptotic.FordSimplexRows
import OAI.NumberTheory.TotientAsymptotic.Normalization

namespace OAI

/-! The complete unnormalized exceptional-value bound in Ford Theorem 16. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma large_head_coordinate_gt_two : ∀ᶠ x : ℝ in atTop,∀ n : ℕ,
    x^(1/4:ℝ) ≤ fordPrime n 0 → 2 < fordPrimeCoordinate n 0 := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually
    (eventually_gt_atTop (Real.exp (Real.exp 2)))] with x hx
  intro n hn
  by_contra hh
  have hu := ford_prime_le_exp_exp (by norm_num) (le_of_not_gt hh)
  linarith only [hx,hn,hu]

theorem ford_structure_value_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ < m x → ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ (v:ℝ) ≤ x ∧ ¬fordSimplexCondition x Ψ (n v)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,htop⟩ := top_row_failure_count
  obtain ⟨E,hE,hfirst⟩ := first_failed_rows_tail_bound
  obtain ⟨F,hF,htail⟩ := small_terminal_tail_count
  refine ⟨A+D+E+F,by positivity,?_⟩
  filter_upwards [hsmall,htop,hfirst,htail,large_head_coordinate_gt_two,all_preimages_second_coordinate]
    with x hs ht hf hu hhead hsecond
  intro Ψ hΨ Q n hQ
  let H := Q.filter (fun v => (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ))
  let T := Q.filter (fun v => ¬fordRowHolds x (n v) 0)
  let Fst := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
    ∃ j,1 ≤ j ∧ j ≤ m x-Ψ ∧ FirstFailedRowAt x (n v) j)
  let U := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
    2 < fordPrimeCoordinate (n v) 0 ∧ fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 ∧
    ∀ i ≤ m x-Ψ,fordRowHolds x (n v) i)
  have hH := hs Ψ hΨ.le H (by
    intro v hv
    obtain ⟨hv,hhead⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨⟨n v,hn,hφ⟩,hvx,n v,hn,hφ,hhead⟩)
  have hT := ht Ψ hΨ.le T (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    refine ⟨n v,hn,hφ,hvx,?_⟩
    simpa only [fordRowHolds,ite_true] using not_le.mp hbad)
  have hFst := hf Ψ Fst n (by
    intro v hv
    obtain ⟨hv,hlarge,hfirst⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hfirst⟩)
  have hU := hu Ψ U n (by
    intro v hv
    obtain ⟨hv,hlarge,hhead,htail,hrows⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hvx,_⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hhead,htail,hrows⟩)
  have hcover : Q ⊆ H ∪ T ∪ Fst ∪ U := by
    intro v hv
    obtain ⟨hn,hφ,hvx,hbad⟩ := hQ v hv
    by_cases hsmall : (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hsmall⟩)))
    have hlarge : x^(1/4:ℝ) ≤ fordPrime (n v) 0 := le_of_not_gt hsmall
    by_cases htop : fordRowHolds x (n v) 0
    · by_cases hfail : ∃ j,j ≤ m x-Ψ ∧ ¬fordRowHolds x (n v) j
      · have hfirst := first_failed_row_exists htop hfail
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hlarge,hfirst⟩))
      · have hrows : ∀ i ≤ m x-Ψ,fordRowHolds x (n v) i := by
          intro i hi
          by_contra hh
          exact hfail ⟨i,hi,hh⟩
        have htail : fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 := by
          by_contra hh
          apply hbad
          exact ford_simplex_of_full_rows hΨ (lt_of_not_ge hh)
            (hsecond (n v) hn (by simpa only [hφ] using hvx))
            (fun i hi => hrows i hi.le)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hv,hlarge,hhead (n v) hlarge,htail,hrows⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv,htop⟩)))
  have hc : (Q.card:ℝ) ≤ H.card+T.card+Fst.card+U.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  calc
    _ ≤ (H.card:ℝ)+T.card+Fst.card+U.card := hc
    _ ≤ A*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        D*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        E*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        F*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
      linarith only [hH,hT,hFst,hU]
    _ = _ := by ring

theorem ford_structure_exception_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ < m x →
    preimageExceptionCount x (fordSimplexCondition x Ψ) ≤
      C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨C,hC,hcount⟩ := ford_structure_value_count
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (0:ℝ)] with x hx hx0
  intro Ψ hΨ
  let Q := preimageExceptionValues x (fordSimplexCondition x Ψ)
  have hw (v : {v // v ∈ Q}) : ∃ n : ℕ,0 < n ∧ n.totient=v.val ∧
      ¬fordSimplexCondition x Ψ n := (Finset.mem_filter.mp v.property).2
  choose n hn using hw
  let f : ℕ → ℕ := fun v => if hv : v ∈ Q then n ⟨v,hv⟩ else 1
  apply hx Ψ hΨ Q f
  intro v hv
  have hvx : (v:ℝ) ≤ x := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hx0)
  have hh := hn ⟨v,hv⟩
  simpa only [f,dite_eq_left hv] using ⟨hh.1,hh.2.1,hvx,hh.2.2⟩

/-- The structural published input now needs only the separately named
counting-scale lower bound; its exceptional-set argument is internal. -/
theorem fordTheorem16_of_scale (hscale : FordScaleBounds) : FordTheorem16Input := by
  obtain ⟨c,_,hc,hscale⟩ := hscale
  obtain ⟨C,hC,hcount⟩ := ford_structure_exception_count
  refine ⟨C/c,div_pos hC hc,?_⟩
  filter_upwards [hscale,hcount,scale_eventually_pos] with x hs hx hnorm
  intro Ψ hΨ
  have hmass : c*(x/Real.log x*G x (m x)) ≤ V x := by
    have hh := (le_div_iff₀ hnorm).mp hs.1
    exact hh
  have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ C/c by positivity)
  have he : C*(x/Real.log x)*G x (m x) ≤ (C/c)*V x := by
    have hid : (C/c)*(c*(x/Real.log x*G x (m x)))=C*(x/Real.log x)*G x (m x) := by
      field_simp
    rwa [hid] at hh
  exact (hx Ψ hΨ).trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)

end TotientAsymptotic

end

end OAI
