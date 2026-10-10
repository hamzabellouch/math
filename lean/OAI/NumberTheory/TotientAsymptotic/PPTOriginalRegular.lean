import OAI.NumberTheory.TotientAsymptotic.PPTHeadWitness
import OAI.NumberTheory.TotientAsymptotic.LocalOriginalComparisonData
import OAI.NumberTheory.TotientAsymptotic.LocalPrimeRoughness
import OAI.NumberTheory.TotientAsymptotic.SuffixSize

namespace OAI

/-! The actual original-head regular class satisfies the finite comparison bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem ppt_original_regular_count {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ F : ℕ→ℕ,let R:=localOriginalBad x c d L H
      (∀ r∈R,0 < F r ∧ (F r).totient=d*r.totient ∧ ¬r∣F r ∧
        largestPrimeFactor (F r)≠largestPrimeFactor r) →
      ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  let A : ℝ := 1/lam+2
  have hA : 0 < A := by have hlam := lam_pos; dsimp only [A]; positivity
  filter_upwards [local_original_comparison_data hc d hd L,
    local_normal_candidate_normality_and_value hc d hd L] with H hdata hvalues
  filter_upwards [hdata,hvalues,ppt_regular_head_witness d hd hA,
    ppt_witnessed_residual_count d hd hA 4,m_le_log_B,
    m_tendsto.eventually (eventually_ge_atTop 1),
    (localNormalityScale_tendsto.comp m_tendsto).eventually
      (eventually_ge_atTop (largestPrimeFactor d:ℝ)),
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)]
    with x hdata hvalues hwitness hcount hdim hm hseed hB hx
  intro F R hF
  let T:=localWitnessRegular R F (m x)
  let S:=localNormalityScale (m x)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have ht : 0 < B x := (Real.exp_pos 1).trans_le hB
  have hlog : 1 ≤ Real.log (B x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  have hdim' : ((m x+1:ℕ):ℝ) ≤ A*Real.log (B x) := by
    dsimp only [A]
    push_cast
    have he : (1/lam+2)*Real.log (B x)=Real.log (B x)/lam+2*Real.log (B x) := by ring
    rw [he]
    linarith only [hdim,hlog]
  have hS : Real.exp (Real.exp 1) ≤ S := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    have hmr : (1:ℝ) ≤ m x := by exact_mod_cast hm
    exact one_le_pow₀ hmr
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : B S=(m x:ℝ)^4 := by simp only [S,localNormalityScale,B,Real.log_exp]
  have hBS0 : 0 ≤ B S := by rw [hBS]; positivity
  have hheight : B S ≤ ((m x+1:ℕ):ℝ)^4 := by
    rw [hBS]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 4
  have hTR : T⊆R := by intro r hr; exact (local_regular_witness_properties hr).1
  have hTN (r) (hr : r∈T) : r∈localNormalCandidates x c d L H :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hTR hr)).1).1
  have hsmall : (T.card:ℝ) ≤ x/((d:ℝ)*Real.log x)*(B x)^(-4:ℝ) := by
    apply hcount (m x-H+1) (m x+1) S T hdim' hS1 hBS0
    intro r hr
    obtain ⟨p,q,he,hp,ho,hgeom,hq,hqp,_htail,hhead,hqn,hpn,hq3,hp3,hcap⟩ :=
      hdata r (hTN r hr)
    let P : Fin (m x-H+1)→ℕ := Fin.cons q p
    let v := primePrefixCoord p
    let ι : Fin ((m x-H+1)-1)↪o Fin (m x-H) :=
      (Fin.castOrderIso (by omega)).toOrderEmbedding
    have hP (i) : IsNormalPrime S (P i) := by
      refine Fin.cases hqn (fun j=>hpn j) i
    have hP3 (i) : 3 ≤ P i := by
      refine Fin.cases hq3 (fun j=>hp3 j) i
    have hPo : StrictAnti P := (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr ⟨hqp,ho⟩
    have hPp (i) : (P i).Prime := (hP i).1
    have hprod : r=∏ i,P i := by simpa only [P,Fin.prod_cons] using he
    have hrpos : 0 < r := by rw [hprod]; exact Finset.prod_pos (fun i _=>(hPp i).pos)
    have hpred (i) : (P i-1:ℕ) ≤ x := by
      have hdiv : P i∣r := by rw [hprod]; exact Finset.dvd_prod_of_mem P (Finset.mem_univ i)
      exact (Nat.cast_le.mpr (prime_predecessor_le_seed_totient hrpos (hPp i) hdiv hd)).trans
        (hvalues r (hTN r hr)).1
    have hcap' (i : Fin (m x-H+1)) (hi : 0 < i.val) : B (P i) ≤ (4/5:ℝ)*B x := by
      let j : Fin (m x-H) := ⟨i.val-1,by have := i.isLt; omega⟩
      have heq : j.succ=i := by
        apply Fin.ext
        change (i.val-1)+1=i.val
        omega
      rw [←heq]
      change B (p j) ≤ _
      exact (hcap j).trans (mul_le_mul_of_nonneg_right (by norm_num : (19/25:ℝ) ≤ 4/5) ht.le)
    have hcoords (i : Fin ((m x-H+1)-1)) : v (ι i)=B (P ⟨i.val+1,by omega⟩) := by
      let j : Fin (m x-H) := ι i
      have heq : j.succ=(⟨i.val+1,by omega⟩ : Fin (m x-H+1)) := by apply Fin.ext; rfl
      rw [←heq]
      rfl
    have hregular := local_regular_witness_properties hr
    have hvalue := hF r (hTR hr)
    apply hwitness (m x) (m x-H) (m x-H+1) (m x+1) (F r) r P v ι
      (B x) (c/2) S (by omega) (Nat.sub_le _ _) (by omega) hdim' le_rfl
      (by linarith) hgeom hcoords hcap' hS hheight hP hP3 hPo
      hvalue.1 hvalue.2.1 hprod hseed hregular.2.2.1 hregular.2.2.2 hregular.2.1
    · rw [←ordered_prime_product_largest (by omega) P hPp hPo,←hprod]
      exact hvalue.2.2.2
    · exact hpred
    · rw [hvalue.2.1]
      exact (hvalues r (hTN r hr)).1
    · change x^(9/10:ℝ) ≤ (q:ℝ)
      exact hhead.le
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply div_le_div_of_nonneg_left hx0.le (Real.log_pos hx)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 (Real.log_pos hx).le

end TotientAsymptotic

end

end OAI
