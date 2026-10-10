import OAI.Combinatorics.PerfectMatching.AlgorithmPartition

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def edgeWeight (G : Input) (e : Pair G.n) : ℝ := Real.exp (Real.log 2*(beta G e:ℝ))
def matchingWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  ∏ e∈M.val,edgeWeight G e

def validMatching (G : Input) (M : (completeGraph G.n).Matching) : Prop :=
  ∀ e∈M.val,0< multiplicity G e

def goodWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) (matchingWeight G M) 0

def badWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) 0 (matchingWeight G M)

def Zgood (G : Input) : ℝ := ∑ M,goodWeight G M
def Zbad (G : Input) : ℝ := ∑ M,badWeight G M

def multProduct (G : Input) (M : (completeGraph G.n).Matching) : ℕ :=
  ∏ e∈M.val,multiplicity G e

lemma matchingWeight_exp (G : Input) (M : (completeGraph G.n).Matching) :
    matchingWeight G M=Real.exp (Real.log 2*((completeGraph G.n).score (fun e => (beta G e:ℝ)) M)) := by
  rw [LooplessGraph.score,mul_sum,Real.exp_sum]
  rfl

lemma matchingWeight_pos (G : Input) (M : (completeGraph G.n).Matching) : 0< matchingWeight G M := by
  rw [matchingWeight_exp]; exact Real.exp_pos _

lemma Z_decompose (G : Input) : Z G=Zgood G+Zbad G := by
  unfold Z LooplessGraph.weightedZ expSum Zgood Zbad
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro M _
  rw [←matchingWeight_exp]
  unfold goodWeight badWeight
  split_ifs <;> simp

lemma goodWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ goodWeight G M := by
  unfold goodWeight; split_ifs
  · exact (matchingWeight_pos G M).le
  · rfl

lemma badWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ badWeight G M := by
  unfold badWeight; split_ifs
  · rfl
  · exact (matchingWeight_pos G M).le

lemma Zgood_nonneg (G : Input) : 0≤ Zgood G := sum_nonneg fun M _ => goodWeight_nonneg G M
lemma Zbad_nonneg (G : Input) : 0≤ Zbad G := sum_nonneg fun M _ => badWeight_nonneg G M

lemma edgeWeight_present (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    edgeWeight G e=(2:ℝ)^Nat.log2 (multiplicity G e) := by
  rw [edgeWeight,beta,ite_eq_right (by omega),Int.cast_natCast,mul_comm,Real.exp_nat_mul]
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]

lemma edgeWeight_rounding (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    (multiplicity G e:ℝ)/2≤ edgeWeight G e ∧ edgeWeight G e≤(multiplicity G e:ℝ) := by
  rw [edgeWeight_present G e he]
  have hlo := Nat.log2_self_le (show multiplicity G e≠0 by omega)
  have hhi : multiplicity G e<2^(Nat.log2 (multiplicity G e)+1) := Nat.lt_log2_self
  have hlo' : (2:ℝ)^Nat.log2 (multiplicity G e)≤(multiplicity G e:ℝ) := by exact_mod_cast hlo
  have hhi' : (multiplicity G e:ℝ)<(2:ℝ)^(Nat.log2 (multiplicity G e)+1) := by exact_mod_cast hhi
  rw [pow_succ] at hhi'
  constructor <;> linarith

lemma invalid_product_zero (G : Input) (M : (completeGraph G.n).Matching)
    (hM : ¬validMatching G M) : multProduct G M=0 := by
  classical
  unfold validMatching at hM
  push Not at hM
  obtain ⟨e,he,hzero⟩ := hM
  unfold multProduct
  exact prod_eq_zero he (by omega)

lemma goodWeight_le_product (G : Input) (M : (completeGraph G.n).Matching) :
    goodWeight G M≤(multProduct G M:ℝ) := by
  unfold goodWeight
  split_ifs with hM
  · unfold matchingWeight multProduct
    push_cast
    exact prod_le_prod₀ (fun e _ => (Real.exp_pos _).le)
      (fun e he => (edgeWeight_rounding G e (hM e he)).2)
  · positivity

lemma goodWeight_ge_product (G : Input) (M : (completeGraph G.n).Matching) :
    (2:ℝ)⁻¹^M.val.card*(multProduct G M:ℝ)≤ goodWeight G M := by
  unfold goodWeight
  split_ifs with hM
  · calc
      _ = ∏ e∈M.val,((multiplicity G e:ℝ)/2) := by
        simp only [div_eq_mul_inv,prod_mul_distrib,prod_const,multProduct,Nat.cast_prod]
        ring
      _ ≤ _ := prod_le_prod₀ (fun e _ => by positivity)
        (fun e he => (edgeWeight_rounding G e (hM e he)).1)
  · rw [invalid_product_zero G M hM,Nat.cast_zero,mul_zero]

lemma Zgood_bracket (G : Input) {r : ℕ} (hn : G.n=2*r) :
    (2:ℝ)⁻¹^r*(count G:ℝ)≤ Zgood G ∧ Zgood G≤(count G:ℝ) := by
  have hc (M : (completeGraph G.n).Matching) : M.val.card=r :=
    (completeGraph G.n).matching_card (by simpa) M
  have hncast : (count G:ℝ)=∑ M,(multProduct G M:ℝ) := by simp [count,multProduct]
  rw [hncast]
  constructor
  · rw [mul_sum]
    exact sum_le_sum fun M _ => by simpa only [hc M] using goodWeight_ge_product G M
  · exact sum_le_sum fun M _ => goodWeight_le_product G M

lemma positive_count_valid (G : Input) (hN : 0< count G) :
    ∃ M : (completeGraph G.n).Matching, validMatching G M := by
  have hsum : 0<∑ M,multProduct G M := hN
  obtain ⟨M,_hM,hprod⟩ := (sum_pos_iff_of_nonneg (fun M _ => Nat.zero_le (multProduct G M))).mp hsum
  refine ⟨M,?_⟩
  by_contra h
  rw [invalid_product_zero G M h] at hprod
  omega

lemma validWeight_ge_one (G : Input) (M : (completeGraph G.n).Matching)
    (hM : validMatching G M) : 1≤ goodWeight G M := by
  rw [goodWeight,ite_eq_left hM]
  apply one_le_prod₀
  intro e he
  rw [edgeWeight_present G e (hM e he)]
  exact one_le_pow₀ (by norm_num)

lemma Zgood_ge_one (G : Input) (hN : 0< count G) : 1≤ Zgood G := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  exact (validWeight_ge_one G M hM).trans
    (single_le_sum (fun N _ => goodWeight_nonneg G N) (mem_univ M))

lemma beta_le_B (G : Input) (e : Pair G.n) : (beta G e:ℝ)≤(B G:ℝ) := by
  unfold beta
  split_ifs
  · simp only [Int.cast_neg,Int.cast_natCast]
    have : (0:ℝ)≤ B G := by positivity
    have : (0:ℝ)≤ L G := by positivity
    linarith
  · exact_mod_cast multiplicity_log_le_B G e

lemma matching_card_bound (n : ℕ) : Fintype.card (completeGraph n).Matching≤2^(q n) := by
  calc
    _ ≤ Fintype.card (Finset (Pair n)) :=
      Fintype.card_le_of_injective (fun M => M.val) Subtype.val_injective
    _ = _ := by rw [Fintype.card_finset]; rfl

lemma badWeight_bound (G : Input) {r : ℕ} (hn : G.n=2*r)
    (M : (completeGraph G.n).Matching) :
    badWeight G M≤ Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
  classical
  unfold badWeight
  split_ifs with hM
  · exact (Real.exp_pos _).le
  · have hbad := hM
    unfold validMatching at hbad
    push Not at hbad
    obtain ⟨e,he,hzero⟩ := hbad
    have hz : multiplicity G e=0 := by omega
    have hbe : (beta G e:ℝ)=-(L G:ℝ) := by simp [beta,hz]
    have hc : M.val.card=r := (completeGraph G.n).matching_card (by simpa) M
    have hsingle := single_le_sum (s := M.val) (f := fun e => (B G:ℝ)-(beta G e:ℝ))
      (fun e _ => sub_nonneg.mpr (beta_le_B G e)) he
    rw [hbe,sum_sub_distrib,sum_const,hc,nsmul_eq_mul] at hsingle
    have hB : (0:ℝ)≤ B G := by positivity
    have hsum : (∑ e∈M.val,(beta G e:ℝ))≤(B G:ℝ)*r-L G := by nlinarith
    rw [matchingWeight_exp]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsum log_two_pos.le

lemma Zbad_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    Zbad G≤ Real.exp (Real.log 2*((q G.n:ℝ)+(B G:ℝ)*r-L G)) := by
  calc
    _ ≤ ∑ _M : (completeGraph G.n).Matching, Real.exp (Real.log 2*((B G:ℝ)*r-L G)) :=
      sum_le_sum fun M _ => badWeight_bound G hn M
    _ = (Fintype.card (completeGraph G.n).Matching:ℝ)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by simp
    _ ≤ (2:ℝ)^(q G.n)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast matching_card_bound G.n
    _ = _ := by
      have he : (2:ℝ)^(q G.n)=Real.exp ((q G.n:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma completion_parameter_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    q G.n+B G*r+20*G.n≤ L G := by
  let t := G.n+B G+1
  have ht1 : 1≤ t := by dsimp [t]; omega
  have hnt : G.n≤ t := by dsimp [t]; omega
  have hBt : B G≤ t := by dsimp [t]; omega
  have hrt : r≤ t := by omega
  have hq : q G.n≤ t^2 := (q_le_square (n := G.n)).trans (Nat.pow_le_pow_left hnt 2)
  have hBr : B G*r≤ t^2 := by simpa only [pow_two] using Nat.mul_le_mul hBt hrt
  have ht13 : t≤ t^3 := Nat.le_self_pow (by omega) t
  have ht23 : t^2≤ t^3 := by
    calc
      t^2=t^2*1 := by ring
      _ ≤ t^2*t := Nat.mul_le_mul_left _ ht1
      _ = _ := by ring
  change _≤100*t^3
  omega

lemma Zbad_small (G : Input) (heven : Even G.n) :
    Zbad G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by
  obtain ⟨r,hr⟩ := heven
  have hn : G.n=2*r := by omega
  have hh := Zbad_bound G hn
  have hdom : (q G.n:ℝ)+(B G:ℝ)*r+20*(G.n:ℝ)≤ L G := by
    exact_mod_cast completion_parameter_bound G hn
  apply hh.trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ log_two_pos.le
  linarith

theorem completion_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (count G=0 → logZ G≤-20*(G.n:ℝ)) ∧
    (0< count G → 1≤ Z G ∧ (2:ℝ)⁻¹^(G.n/2)*(count G:ℝ)≤ Z G ∧ Z G≤2*(count G:ℝ)) := by
  have hbad := Zbad_small G heven
  have hNsplit := Z_decompose G
  have hsmall : Zbad G≤1 := by
    apply hbad.trans (Real.exp_le_one_iff.mpr _)
    exact mul_nonpos_of_nonneg_of_nonpos log_two_pos.le (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hn2 : G.n=2*(G.n/2) := by
    obtain ⟨r,hr⟩ := heven
    omega
  have hgood := Zgood_bracket G hn2
  constructor
  · intro hN
    have hg : Zgood G=0 := le_antisymm (by simpa only [hN,Nat.cast_zero] using hgood.2) (Zgood_nonneg G)
    have hz : Z G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by linarith
    have hl := Real.log_le_log (Z_pos G hn heven) hz
    rw [Real.log_exp] at hl
    unfold logZ
    apply (div_le_iff₀ log_two_pos).2
    nlinarith
  · intro hN
    have hng : 1≤ Zgood G := Zgood_ge_one G hN
    have hN' : (1:ℝ)≤ count G := by exact_mod_cast hN
    have hbn := Zbad_nonneg G
    constructor
    · linarith
    constructor
    · linarith [hgood.1]
    · linarith [hgood.2]

end
end BinaryMatching.Algorithm
end

end OAI
