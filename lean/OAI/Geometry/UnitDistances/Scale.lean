import OAI.Geometry.UnitDistances.Quantization

namespace OAI

namespace PlanarUnitDistances.FiniteAcceptance
open Finset FiniteLaw CrossPrediction Real MeasureTheory
open scoped Classical
noncomputable section
variable {P Q H C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype C] [Fintype T] [DecidableEq H]

def feature (c : C) : EuclideanSpace ℝ C := WithLp.toLp 2 (Pi.single c 1)
def test (A : C → Prop) : EuclideanSpace ℝ C := WithLp.toLp 2 (fun c => if A c then 1 else 0)

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma feature_inner (c : C) (A : C → Prop) :
    inner ℝ (feature c) (test A)=(if A c then 1 else 0) := by
  rw [PiLp.inner_apply]
  simp [feature,test,RCLike.inner_apply]

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma norm_feature (c : C) : ‖feature c‖ ≤ 1 := by
  have hh : inner ℝ (feature c) (feature c)=1 := by
    rw [PiLp.inner_apply]
    simp [feature]
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (feature c)]

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma norm_test (A : C → Prop) : ‖test A‖ ≤ sqrt (Fintype.card C) := by
  have hh : inner ℝ (test A) (test A) ≤ (Fintype.card C:ℝ) := by
    rw [PiLp.inner_apply]
    calc
      _ ≤ ∑ _ : C,(1:ℝ) := by
        apply sum_le_sum
        intro c _
        simp only [test,WithLp.ofLp_toLp,RCLike.inner_apply,conj_trivial]
        split_ifs <;> norm_num
      _ = _ := by simp
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [sqrt_nonneg (Fintype.card C:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card C))]

omit [Fintype H] [Fintype T] [DecidableEq H] in
def actual (κ : Law Q) (w : Q → Law P) (c : P → C) (A : Q → C → Prop) : ℝ :=
  avg κ (fun q => event (w q) (fun p => A q (c p)))

omit [Fintype T] [DecidableEq H] in
def predicted (κ : Law Q) (w : Q → Law P) (h : P → H) (c : P → C) (A : Q → C → Prop) : ℝ :=
  avg κ (fun q => avg (w q) (fun p => event (cond (mixture κ w) h (h p)) (fun r => A q (c r))))

omit [Fintype T] in
lemma discrepancy_eq (κ : Law Q) (w : Q → Law P) (h : P → H)
    (hμ : ∀p,0 < (mixture κ w).val p) (c : P → C) (A : Q → C → Prop) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h c feature (fun q => test (A q))=
      |actual κ w c A-predicted κ w h c A| := by
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val)=(mixture κ w).val := rfl
  unfold FiniteInformation.testDiscrepancy
  rw [hm]
  simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hμ _),sum_inner,
    real_inner_smul_left,inner_sub_left,sum_inner,real_inner_smul_left,feature_inner]
  simp only [actual,predicted,event,avg]
  congr 1
  simp only [mul_sub,sum_sub_distrib]

omit [Fintype H] [Fintype T] [Fintype C] [DecidableEq H] in
lemma actual_one (κ : Law Q) (w : Q → Law P) (c : P → C) (A : Q → C → Prop)
    (hpass : ∀q p,0 < κ.val q*(w q).val p → A q (c p)) : actual κ w c A=1 := by
  have he : actual κ w c A=avg κ (fun _ => (1:ℝ)) := by
    unfold actual event avg
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro q _
    conv_rhs => rw [←(w q).total, mul_sum]
    apply sum_congr rfl
    intro p _
    by_cases hz : κ.val q*(w q).val p=0
    · rw [←mul_assoc,hz,zero_mul]
    · have hp := lt_of_le_of_ne (mul_nonneg (κ.nonneg q) ((w q).nonneg p)) (Ne.symm hz)
      rw [ite_eq_left (hpass q p hp),mul_one]
  rw [he,avg_const]

omit [Fintype H] [DecidableEq H] in

theorem exists_history [Nonempty C] (κ : Law Q) (w : Q → Law P)
    (hμ : ∀p,0 < (mixture κ w).val p) (σ : Law T)
    (c : T → P → C) (A : T → Q → C → Prop)
    (hpass : ∀t q p,0 < κ.val q*(w q).val p → A t q (c t p))
    (K : ℕ) (hK : 0 < K) :
    ∃n<K,∃h : P → FiniteInformation.History C n,
      (univ.image h).card ≤ (Fintype.card C)^(K-1) ∧
      avg σ (fun t => 1-predicted κ w h (c t) (A t)) ≤
        4*sqrt (Fintype.card C)*(FiniteInformation.KL
          (FiniteInformation.wedge κ.val (fun q => (w q).val))
          (fun pp : P×P => (mixture κ w).val pp.1*(mixture κ w).val pp.2)/(K:ℝ))^(1/4:ℝ) := by
  let : MeasurableSpace C := ⊤
  let : MeasurableSpace T := ⊤
  have hδ : ∀n,Measurable (fun z : (P → FiniteInformation.History C n)×T =>
      FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) z.1
        (c z.2) feature (fun q => test (A z.2 q))) := by
    intro n
    let := history_singleton C n
    exact measurable_of_finite _
  obtain ⟨n,hn,h,hcard,hb⟩ := FiniteInformation.exists_prediction_history
    (ν := σ.pmf.toMeasure) κ.val (fun q => (w q).val) κ.nonneg (fun q => (w q).nonneg)
    κ.total (fun q => (w q).total) c (fun _ => feature) (fun t q => test (A t q))
    (fun _ => measurable_of_finite _) hδ (by norm_num : (0:ℝ) ≤ 1)
    (sqrt_nonneg (Fintype.card C)) (fun _ => norm_feature) (fun t q => norm_test (A t q)) K hK
  refine ⟨n,hn,h,hcard,?_⟩
  rw [integral_pmf] at hb
  simp only [discrepancy_eq κ w h hμ,actual_one κ w _ _ (hpass _),mul_one] at hb
  exact (avg_mono σ (fun t => le_abs_self (1-predicted κ w h (c t) (A t)))).trans hb
end
end PlanarUnitDistances.FiniteAcceptance

namespace PlanarUnitDistances.BoundedScaleFinite
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues BoundedProbabilities FiniteQuantization EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

theorem obstruction (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (hE : ∀p q,0<π.val (p,q) → E p q)
    (hu : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (hZinj : Function.Injective Z) (hainj : Function.Injective a)
    {C B τ δ d m : ℝ} (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hmesh : τ < δ^4/(128*B^5))
    (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (hW : avg (left π) (fun p => exactHeight K (W p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C)
    (hb : avg (right π) (fun q => exactHeight K (b q)) ≤ C)
    (hD : avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C)
    (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hp : ∀p,(left π).val p ≤ d) (hq : ∀p q,(row π p).val q ≤ m) :
    1 ≤ 11*C/Real.log B+10*(2*C+Real.log 2)/Real.log (1/δ)+
      (Fintype.card H:ℝ)*d+9*m+3*BoundedProbabilities.failure π h Z W E B τ := by
  let μ := pair (law π h) (uniform (Embeddings K))
  have hall : event μ (fun x => ∃i,bad Z W a b E B τ δ i x)=1 := by
    calc
      _ = event μ (fun _ => True) := event_congr μ (fun x => iff_true_intro
        (cover Z W a b E hu hZinj hainj hB hτ hτ₁ hδ hmesh x))
      _ = 1 := event_true μ
  have hh := event_exists_le μ (bad Z W a b E B τ δ)
  rw [hall] at hh
  have h0 := large_bound π h Z W a b (τ := τ) (δ := δ) (show 1<B by linarith) E (big_mean π h Z W a b hZ hW ha hb hD)
  have h1 := small_bound π h Z W a b (B := B) (τ := τ) hδ hδ₁ E (small_mean π h Z a hZ ha)
  have h2 := point_bound π h Z W a b E B τ δ hd hp
  have h3 := centers_bound π h Z W a b E B τ δ hm hq
  have h4 := nonedge_zero π h Z W a b E hE B τ δ
  have h5 := failure_bound π h Z W a b E B τ δ
  norm_num [Fin.sum_univ_succ,Fin.succ] at hh
  change 1 ≤
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 0) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 1) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4) +
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 5))))) at hh
  linarith

omit [Fintype H] in
def information (π : Law (P×Q)) : ℝ :=
  FiniteInformation.KL (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
    (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)

omit [Fintype H] in
theorem exists_small_failure (π : Law (P×Q)) (Z W : P → K) (E : P → Q → Prop)
    (hE : ∀p q,0<π.val (p,q) → E p q) (hμ : ∀p,0<(left π).val p)
    (B τ : ℝ) (k : ℕ) (hk : 0<k) :
    ∃n<k,∃h : P → FiniteInformation.History (Alphabet B τ) n,
      BoundedProbabilities.failure π h Z W E B τ ≤
        4*Real.sqrt (Fintype.card (Alphabet B τ))*
          (information π/(k:ℝ))^(1/4:ℝ) := by
  let c : Embeddings K → P → Alphabet B τ := fun σ p => code B τ (σ (Z p)) (σ (W p))
  let A : Embeddings K → Q → Alphabet B τ → Prop := fun σ q v => ∃s,E s q ∧ v=c σ s
  have hm : ∀p,0<(mixture (right π) (col π)).val p := by rwa [mixture_col]
  have hp : ∀σ q p,0<(right π).val q*(col π q).val p → A σ q (c σ p) := by
    intro σ q p hi
    rw [col_weight] at hi
    exact ⟨p,hE p q hi,rfl⟩
  obtain ⟨n,hn,h,_,hb⟩ := FiniteAcceptance.exists_history (right π) (col π) hm
    (uniform (Embeddings K)) c A hp k hk
  refine ⟨n,hn,h,?_⟩
  have hf : BoundedProbabilities.failure π h Z W E B τ =
      avg (uniform (Embeddings K)) (fun σ => 1-FiniteAcceptance.predicted (right π) (col π) h (c σ) (A σ)) := by
    unfold BoundedProbabilities.failure FiniteAcceptance.predicted
    rw [mixture_col]
    apply avg_congr
    intro σ
    simp only [event_compl,avg_sub,avg_const]
    rfl
  rw [hf]
  simpa only [mixture_col,information] using hb
end
end PlanarUnitDistances.BoundedScaleFinite

namespace PlanarUnitDistances.BoundedConstants
noncomputable section

theorem exists_cutoffs (C : ℝ) (hC : 0 ≤ C) :
    ∃B τ δ : ℝ,2 ≤ B ∧ 0 < τ ∧ τ ≤ 1 ∧ 0 < δ ∧ δ < 1 ∧
      τ < δ^4/(128*B^5) ∧
      11*C/Real.log B+10*(2*C+Real.log 2)/Real.log (1/δ) ≤ 1/4 := by
  let X := 1000*(C+1)
  let Y := 1000*(2*C+Real.log 2+1)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  let B := Real.exp X
  let δ := Real.exp (-Y)
  have hB : 2 ≤ B := by
    have he := Real.add_one_le_exp X
    dsimp [B,X] at *
    linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδ₁ : δ < 1 := by exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hY)
  have hm : 0 < δ^4/(128*B^5) := div_pos (pow_pos hδ _) (mul_pos (by norm_num) (pow_pos (by linarith) _))
  let τ := min (1/2:ℝ) (δ^4/(128*B^5)/2)
  refine ⟨B,τ,δ,hB,lt_min (by norm_num) (half_pos hm),?_,hδ,hδ₁,?_,?_⟩
  · exact (min_le_left _ _).trans (by norm_num)
  · exact (min_le_right _ _).trans_lt (half_lt_self hm)
  · have hLB : Real.log B=X := Real.log_exp _
    have hLD : Real.log (1/δ)=Y := by simp [δ,Real.log_inv]
    rw [hLB,hLD]
    have hx : 11*C/X ≤ 11/1000 := by
      apply (div_le_iff₀ hX).mpr
      dsimp [X]
      nlinarith
    have hy : 10*(2*C+Real.log 2)/Y ≤ 10/1000 := by
      apply (div_le_iff₀ hY).mpr
      dsimp [Y]
      nlinarith
    linarith
end
end PlanarUnitDistances.BoundedConstants

namespace PlanarUnitDistances.BoundedScaleUniform
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues FiniteQuantization
open scoped Classical
noncomputable section

theorem obstruction (C : ℝ) (hC : 0 ≤ C) :
    ∃M : ℕ,0<M ∧ ∀(P Q K : Type) [Fintype P] [Fintype Q]
      [Field K] [NumberField K] [IsGalois ℚ K],
    ∀(π : Law (P×Q)) (Z W : P → K) (a b : Q → K) (E : P → Q → Prop),
    (∀p q,0<π.val (p,q) → E p q) →
    (∀p q,E p q → (Z p-a q)*(W p-b q)=1) →
    Function.Injective Z → Function.Injective a →
    (∀p,0<(left π).val p) →
    avg (left π) (fun p => exactHeight K (Z p)) ≤ C →
    avg (left π) (fun p => exactHeight K (W p)) ≤ C →
    avg (right π) (fun q => exactHeight K (a q)) ≤ C →
    avg (right π) (fun q => exactHeight K (b q)) ≤ C →
    avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C →
    ∀d m : ℝ,0 ≤ d → 0 ≤ m →
    (∀p,(left π).val p ≤ d) → (∀p q,(row π p).val q ≤ m) →
    ∀k : ℕ,0<k →
      3/4 ≤ (M:ℝ)^k*d+9*m+12*Real.sqrt M*(BoundedScaleFinite.information π/(k:ℝ))^(1/4:ℝ) := by
  obtain ⟨B,τ,δ,hB,hτ,hτ₁,hδ,hδ₁,hmesh,htail⟩ := BoundedConstants.exists_cutoffs C hC
  let M := Fintype.card (Alphabet B τ)
  have hM : 0<M := Fintype.card_pos
  refine ⟨M,hM,?_⟩
  intro P Q K _ _ _ _ _ π Z W a b E hE hu hZi hai hμ hZ hW ha hb hD d m hd hm hp hq k hk
  obtain ⟨n,hn,h,hfail⟩ := BoundedScaleFinite.exists_small_failure π Z W E hE hμ B τ k hk
  have hh := BoundedScaleFinite.obstruction π h Z W a b E hE hu hZi hai hB hτ hτ₁ hδ hδ₁ hmesh
    hZ hW ha hb hD hd hm hp hq
  have hc : (Fintype.card (FiniteInformation.History (Alphabet B τ) n):ℝ) ≤ (M:ℝ)^k := by
    rw [FiniteInformation.history_card]
    norm_cast
    exact Nat.pow_le_pow_right hM (Nat.le_of_lt hn)
  have hcd := mul_le_mul_of_nonneg_right hc hd
  change BoundedProbabilities.failure π h Z W E B τ ≤
    4*Real.sqrt M*(BoundedScaleFinite.information π/(k:ℝ))^(1/4:ℝ) at hfail
  linarith
end
end PlanarUnitDistances.BoundedScaleUniform

namespace PlanarUnitDistances.LogHistory
open Filter
noncomputable section

def length (M : ℕ) (t : ℝ) : ℕ := ⌊Real.log t/(4*(Real.log M+1))⌋₊+1

lemma length_pos (M : ℕ) (t : ℝ) : 0<length M t := Nat.succ_pos _

lemma bounds {M : ℕ} (hM : 0<M) {t : ℝ} (ht : 1<t) :
    Real.log t/(4*(Real.log M+1)) ≤ (length M t:ℝ) ∧
      (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 ∧
      (M:ℝ)^(length M t) ≤ M*t^(1/4:ℝ) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hp : (0:ℝ)<M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have ht0 : 0<t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hf := Nat.floor_le (div_nonneg hlt ha.le)
  have hg := Nat.lt_floor_add_one (Real.log t/(4*(Real.log M+1)))
  have hk : (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 := by
    simp only [length,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨by simpa only [length,Nat.cast_add,Nat.cast_one] using hg.le,hk,?_⟩
  have hcoef : Real.log M/(4*(Real.log M+1)) ≤ 1/4 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  have he : (length M t:ℝ)*Real.log M ≤ Real.log M+(1/4:ℝ)*Real.log t := by
    have hh := mul_le_mul_of_nonneg_right hk hl
    have hj := mul_le_mul_of_nonneg_right hcoef hlt
    nlinarith [show Real.log t/(4*(Real.log M+1))*Real.log M=
      (Real.log M/(4*(Real.log M+1)))*Real.log t by ring]
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_nat_mul,Real.exp_log hp,Real.exp_add,Real.exp_log hp] at hh
  simpa only [Real.rpow_def_of_pos ht0,mul_comm (Real.log t) (1/4:ℝ)] using hh

lemma ratio_limit {M : ℕ} (hM : 0<M) (t D : ℕ → ℝ)
    (ht : Tendsto t atTop atTop)
    (hD0 : ∀ᶠn in atTop,0 ≤ D n)
    (hD : Tendsto (fun n => D n/Real.log (t n)) atTop (nhds 0)) :
    Tendsto (fun n => D n/(length M (t n):ℝ)) atTop (nhds 0) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have hupper : Tendsto (fun n => (4*(Real.log M+1))*(D n/Real.log (t n))) atTop (nhds 0) := by
    simpa only [mul_zero] using hD.const_mul (4*(Real.log M+1))
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hD0] with n hn
    exact div_nonneg hn (Nat.cast_nonneg _)
  · filter_upwards [hD0,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).1
    have hk : (0:ℝ)<length M (t n) := by exact_mod_cast length_pos M (t n)
    have hlt : 0<Real.log (t n) := Real.log_pos htn
    have hh : Real.log (t n) ≤ (length M (t n):ℝ)*(4*(Real.log M+1)) := (div_le_iff₀ ha).mp hb
    apply (div_le_iff₀ hk).mpr
    have he : (4*(Real.log M+1))*(D n/Real.log (t n))*(length M (t n):ℝ)=
        D n*((length M (t n):ℝ)*(4*(Real.log M+1)))/Real.log (t n) := by ring
    rw [he]
    apply (le_div_iff₀ hlt).mpr
    exact mul_le_mul_of_nonneg_left hh hdn

lemma density_limit {M : ℕ} (hM : 0<M) (t d : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) (hd0 : ∀ᶠn in atTop,0 ≤ d n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ)) :
    Tendsto (fun n => (M:ℝ)^(length M (t n))*d n) atTop (nhds 0) := by
  have hv : Tendsto (fun n => (M:ℝ)*t n^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply,neg_div] using ((_root_.tendsto_rpow_neg_atTop (y := (1/4:ℝ)) (by norm_num)).comp ht).const_mul (M:ℝ)
  apply squeeze_zero' _ _ hv
  · filter_upwards [hd0] with n hn
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _) hn
  · filter_upwards [hd,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).2.2
    calc
      _ ≤ (M:ℝ)^(length M (t n))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_left hdn (pow_nonneg (Nat.cast_nonneg M) _)
      _ ≤ ((M:ℝ)*t n^(1/4:ℝ))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [mul_assoc,←Real.rpow_add (by linarith : 0<t n)]; norm_num
end
end PlanarUnitDistances.LogHistory

namespace PlanarUnitDistances.BoundedScaleExclusion
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues Filter
open scoped Classical
noncomputable section

lemma information_nonneg {P Q : Type} [Fintype P] [Fintype Q] (π : Law (P×Q)) :
    0 ≤ BoundedScaleFinite.information π := by
  have h := FiniteInformation.KL_nonneg _ _
    (FiniteInformation.wedge_nonneg _ _ (right π).nonneg (fun q => (col π q).nonneg))
    (fun pr : P×P => mul_nonneg ((mixture (right π) (col π)).nonneg pr.1)
      ((mixture (right π) (col π)).nonneg pr.2))
    (FiniteInformation.wedge_sum _ _ (right π).total (fun q => (col π q).total))
    (show ∑pr : P×P,(mixture (right π) (col π)).val pr.1*(mixture (right π) (col π)).val pr.2=1 by
      rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,(mixture (right π) (col π)).total,one_mul])
    (FiniteInformation.wedge_ac _ _ (right π).nonneg (fun q => (col π q).nonneg))
  simpa only [BoundedProbabilities.mixture_col,BoundedScaleFinite.information] using h

theorem no_sequence {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (Z W : ∀n,P n → K n) (a b : ∀n,Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (Z n p-a n q)*(W n p-b n q)=1)
    (hZi : ∀n,Function.Injective (Z n)) (hai : ∀n,Function.Injective (a n))
    (hμ : ∀n p,0<(left (π n)).val p)
    {C : ℝ} (hC : 0 ≤ C)
    (hZ : ∀n,avg (left (π n)) (fun p => exactHeight (K n) (Z n p)) ≤ C)
    (hW : ∀n,avg (left (π n)) (fun p => exactHeight (K n) (W n p)) ≤ C)
    (ha : ∀n,avg (right (π n)) (fun q => exactHeight (K n) (a n q)) ≤ C)
    (hb : ∀n,avg (right (π n)) (fun q => exactHeight (K n) (b n q)) ≤ C)
    (hΔ : ∀n,avg (π n) (fun pq => exactHeight (K n) (Z n pq.1-a n pq.2)) ≤ C)
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    False := by
  obtain ⟨M,hM,hfinite⟩ := BoundedScaleUniform.obstruction C hC
  let k : ℕ → ℕ := fun n => LogHistory.length M (t n)
  have hfirst : Tendsto (fun n => (M:ℝ)^(k n)*d n) atTop (nhds 0) :=
    LogHistory.density_limit hM t d ht (Eventually.of_forall hd0) hd
  have hratio : Tendsto (fun n => BoundedScaleFinite.information (π n)/(k n:ℝ)) atTop (nhds 0) :=
    LogHistory.ratio_limit hM t _ ht (Eventually.of_forall (fun n => information_nonneg (π n))) hinfo
  have hlast : Tendsto (fun n => 12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero] using (hratio.rpow_const_nhds_zero (by norm_num : (0:ℝ)<1/4)).const_mul (12*Real.sqrt M)
  have hsum : Tendsto (fun n => (M:ℝ)^(k n)*d n+9*m n+
      12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using (hfirst.add (hm.const_mul 9)).add hlast
  have hbound : ∀n,3/4 ≤ (M:ℝ)^(k n)*d n+9*m n+
      12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ) := by
    intro n
    exact hfinite (P n) (Q n) (K n) (π n) (Z n) (W n) (a n) (b n) (E n)
      (hE n) (hu n) (hZi n) (hai n) (hμ n) (hZ n) (hW n) (ha n) (hb n) (hΔ n)
      (d n) (m n) (hd0 n) (hm0 n) (hp n) (hq n) (k n) (LogHistory.length_pos M (t n))
  have hh : (3/4:ℝ) ≤ 0 := ge_of_tendsto hsum (Eventually.of_forall hbound)
  norm_num at hh
end
end PlanarUnitDistances.BoundedScaleExclusion

namespace PlanarUnitDistances.ScaleDivergence
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues Filter
open scoped Classical
noncomputable section

theorem not_bounded {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (z w : ∀n,P n⊕Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (z n (.inl p)-z n (.inr q))*(w n (.inl p)-w n (.inr q))=1)
    (hzi : ∀n,Function.Injective (z n ∘ Sum.inl))
    (hzq : ∀n,Function.Injective (z n ∘ Sum.inr))
    (hμ : ∀n p,0<(left (π n)).val p)
    (S : ∀n,Finset (K n))
    (hS : ∀n p q,E n p q → z n (.inl p)-z n (.inr q)∈S n)
    {C R : ℝ} (hc : ∀n,LocalHeightTransfer.LabelControl C (fun p q => (π n).val (p,q)))
    (hR : ∀n,LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)) ≤ R)
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    False := by
  have hn (n : ℕ) := NormalizedScale.coordinates (K n) (π n) (z n) (w n) (E n)
    (hE n) (hu n) (hzi n) (hzq n) (S n) (hS n) (hc n) (hR n)
  choose Z W a b hu' hZi hai hb using hn
  let A := 4*((C+1)*(Real.log 2+2))*(R+1)+4*R+2*Real.log 2
  exact BoundedScaleExclusion.no_sequence π Z W a b E hE hu' hZi hai hμ
    (C := max A 0) (le_max_right _ _)
    (fun n => (hb n).1.trans (le_max_left _ _))
    (fun n => (hb n).2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.2.2.trans (le_max_left _ _))
    t d m ht hd0 hm0 hp hq hd hm hinfo

theorem tends_to_infinity {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (z w : ∀n,P n⊕Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (z n (.inl p)-z n (.inr q))*(w n (.inl p)-w n (.inr q))=1)
    (hzi : ∀n,Function.Injective (z n ∘ Sum.inl))
    (hzq : ∀n,Function.Injective (z n ∘ Sum.inr))
    (hμ : ∀n p,0<(left (π n)).val p)
    (S : ∀n,Finset (K n))
    (hS : ∀n p q,E n p q → z n (.inl p)-z n (.inr q)∈S n)
    {C : ℝ} (hc : ∀n,LocalHeightTransfer.LabelControl C (fun p q => (π n).val (p,q)))
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    Tendsto (fun n => LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)))
      atTop atTop := by
  apply tendsto_atTop.2
  intro R
  by_contra h
  have hh : ∀N : ℕ,∃n,N ≤ n ∧
      LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)) < R := by
    simpa only [eventually_atTop,not_exists,not_forall,not_le,exists_prop] using h
  choose f hf hR using hh
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  exact not_bounded (fun n => π (f n)) (fun n => z (f n)) (fun n => w (f n))
    (fun n => E (f n)) (fun n => hE (f n)) (fun n => hu (f n))
    (fun n => hzi (f n)) (fun n => hzq (f n)) (fun n => hμ (f n))
    (fun n => S (f n)) (fun n => hS (f n)) (fun n => hc (f n)) (fun n => (hR n).le)
    (t ∘ f) (d ∘ f) (m ∘ f) (ht.comp hft) (fun n => hd0 (f n)) (fun n => hm0 (f n))
    (fun n => hp (f n)) (fun n => hq (f n)) (hft.eventually hd) (hm.comp hft) (hinfo.comp hft)
end
end PlanarUnitDistances.ScaleDivergence

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
def graph (n : ℕ) := GeometricLaw.graph (s.P n) (s.Q n) (s.good n).positive
def model (n : ℕ) : CommonFieldModel.Model (s.P n) (s.Q n) :=
  Classical.choice (CommonFieldModel.exists_model (s.good n).algebraicP (s.good n).algebraicQ)
lemma positive (n : ℕ) (p : s.P n) : 0<(left (graph s n)).val p := by
  rw [graph,GeometricLaw.left_eq]
  exact div_pos ((s.good n).point_degree_pos p) (s.good n).positive
lemma positiveQ (n : ℕ) (q : s.Q n) : 0<(right (graph s n)).val q := by
  rw [graph,GeometricLaw.right_eq]
  exact div_pos ((s.good n).center_degree_pos q) (s.good n).positive
lemma support (n : ℕ) (p : s.P n) (q : s.Q n) (h : 0<(graph s n).val (p,q)) :
    GeometricLaw.E (s.P n) (s.Q n) p q := by
  change 0<IncidenceEntropy.indicator (GeometricLaw.E (s.P n) (s.Q n)) p q/_ at h
  by_contra hn
  simp [IncidenceEntropy.indicator,hn] at h
lemma point_bound (n : ℕ) (p : s.P n) : (left (graph s n)).val p≤ s.t n^(-1/2:ℝ) := by
  rw [graph,GeometricLaw.left_eq]
  exact (s.good n).atomUpper p p.property
lemma row_bound (n : ℕ) (p : s.P n) (q : s.Q n) :
    (row (graph s n) p).val q≤1/(s.t n^(1/2:ℝ)) := by
  have hp := (s.good n).point_degree_pos p
  have he := (s.good n).positive
  have hb := (le_div_iff₀ he).mp ((s.good n).atomP p p.property)
  have hd : s.t n^(1/2:ℝ)≤CircleIncidence.degree (s.Q n) p :=
    (s.good n).degreeP.trans (by simpa only [div_mul_eq_mul_div] using hb)
  exact (GeometricLaw.row_le _ _ he p q hp).trans
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [s.large n,Nat.cast_nonneg (α:=ℝ) n]) _) hd)
lemma information_eq (n : ℕ) : BoundedScaleFinite.information (graph s n)=
    IncidenceSequence.information (s.P n) (s.Q n) := by
  unfold BoundedScaleFinite.information IncidenceSequence.information
  rw [graph,GeometricLaw.wedge_eq _ _ _ ((s.good n).center_degree_pos)]
  simp only [GeometricLaw.graph,UniformGraphLaw.left_eq]
lemma label_control : ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
    LocalHeightTransfer.LabelControl C (fun p q => (graph s n).val (p,q)) := by
  obtain ⟨ξ₀,C,hξ,hC,hc⟩ := GlobalLabelControl.constants (by norm_num : (0:ℝ)<27/50)
    (by norm_num : (0:ℝ)<1/25)
  refine ⟨C,hC,?_⟩
  filter_upwards [s.error_limit.eventually_le_const hξ] with n hn
  apply hc (s.P n) (s.Q n) (graph s n)
    (GeometricLaw.counting (s.P n) (GeometricLaw.card_pos _ _ (s.good n).positive).1)
    (GeometricLaw.counting (s.Q n) (GeometricLaw.card_pos _ _ (s.good n).positive).2)
  · intro p
    rw [graph,GeometricLaw.left_eq]
    simpa only [GeometricLaw.counting,mul_one_div] using (s.good n).atomP p p.property
  · intro q
    rw [graph,GeometricLaw.right_eq]
    simpa only [GeometricLaw.counting,mul_one_div] using (s.good n).atomQ q q.property
  · exact (s.good n).error_nonneg
  · exact hn
  · exact GeometricLaw.expansion _ _ (s.good n).positive (s.good n).expansion

def scale (n : ℕ) : ℝ := LevelScale.scale (graph s n) (model s n).support
  (fun pq => (model s n).z (.inl pq.1)-(model s n).z (.inr pq.2))

theorem scale_limit : Tendsto (scale s) atTop atTop := by
  obtain ⟨C,_,hc⟩ := label_control s
  obtain ⟨N,hN⟩ := eventually_atTop.mp hc
  have hf : Tendsto (fun n : ℕ => n+N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
  have ht := s.tendsto.comp hf
  have hm : Tendsto (fun n => 1/(s.t (n+N)^(1/2:ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp ht)
  have hh := ScaleDivergence.tends_to_infinity
    (fun n => graph s (n+N)) (fun n => (model s (n+N)).z) (fun n => (model s (n+N)).w)
    (fun n => GeometricLaw.E (s.P (n+N)) (s.Q (n+N)))
    (fun n => support s (n+N)) (fun n => (model s (n+N)).unit_identity)
    (fun n => (model s (n+N)).point_injective) (fun n => (model s (n+N)).center_injective)
    (fun n => positive s (n+N))
    (fun n => (model s (n+N)).support) (fun n p q _ => (model s (n+N)).sub_mem (.inl p) (.inr q))
    (fun n => hN (n+N) (Nat.le_add_left N n))
    (fun n => s.t (n+N)) (fun n => s.t (n+N)^(-1/2:ℝ))
    (fun n => 1/(s.t (n+N)^(1/2:ℝ))) ht
    (fun n => Real.rpow_nonneg (by linarith [s.large (n+N),Nat.cast_nonneg (α:=ℝ) (n+N)]) _)
    (fun n => div_nonneg zero_le_one (Real.rpow_nonneg (by linarith [s.large (n+N),Nat.cast_nonneg (α:=ℝ) (n+N)]) _)) (fun n => point_bound s (n+N)) (fun n => row_bound s (n+N))
    (Eventually.of_forall (fun _ => le_rfl)) hm
    (by
      simp only [information_eq]
      exact s.information_limit.comp hf)
  exact (tendsto_add_atTop_iff_nat N).mp hh
end
end PlanarUnitDistances.IncidenceScale

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B I : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype I]

lemma bad_good_indicator (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] :
    (if ¬(p ∧ q ∧ r ∧ s) then (1:ℝ) else 0) ≤
      (if ¬p then 1 else 0)+(if ¬q then 1 else 0)+(if ¬r then 1 else 0)+
        (if r ∧ ¬s then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [hp,hq,hr,hs]

def templateLaw (π : Law (P×Q)) (h : P → H) (q : Q) : Law (I → H) :=
  independent (historyLaw π h q) I

def predictionError (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B) : ℝ :=
  avg π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))

def samplingError (k : ℕ) (α : ℝ) : ℝ :=
  (k:ℝ)^2*(1-α)^(k-2)+2*(1-α/2)^(k-1)+(2/α)*(1-α/2)^k

lemma candidate_miss_mean (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B)
    {ε : ℝ} (hε : 0<ε) :
    avg π (fun pq => event (templateLaw (I := I) π h pq.2)
      (fun θ => y pq.2∉Candidates (posteriorState π h x) ε θ))≤
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y := by
  have hc := avg_mono (right π) (fun q => candidate_miss (I := I) (historyLaw π h q)
    (posteriorState π h x) (y q) hε.le)
  rw [avg_smul,avg_smul] at hc
  have he : avg (right π) (fun q => avg (historyLaw π h q)
      (fun v => 1-crossMass (posteriorState π h x v) (y q)))=predictionError π h x y := by
    simp only [historyLaw,push_avg]
    exact col_avg π _
  rw [he] at hc
  have he' : avg (right π) (fun q => event (templateLaw (I := I) π h q)
      (fun θ => y q∉Candidates (posteriorState π h x) ε θ))=
      avg π (fun pq => event (templateLaw (I := I) π h pq.2)
        (fun θ => y pq.2∉Candidates (posteriorState π h x) ε θ)) := push_avg π Prod.snd _
  change ε*avg (right π) (fun q => event (templateLaw (I := I) π h q)
      (fun θ => y q∉Candidates (posteriorState π h x) ε θ))≤_ at hc
  rw [he'] at hc
  rw [mul_comm ε] at hc
  have hd := (le_div_iff₀ hε).mpr hc
  simpa only [div_mul_eq_mul_div] using hd

lemma failure_mean (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    {ε α : ℝ} (hα : 0<α) (hα1 : α<1) (hI : 0<Fintype.card I) (hk : (Fintype.card I:ℝ)*ε<1) :
    avg π (fun pq => event (templateLaw (I := I) π h pq.2)
      (Failure (historyLaw π h pq.2) (posteriorState π h x) ε α))≤
      samplingError (Fintype.card I) α/(1-(Fintype.card I:ℝ)*ε) := by
  apply avg_le_const
  intro pq
  have hs := failure_bound (I := I) (historyLaw π h pq.2) (posteriorState π h x)
    (ε := ε) hα hα1 hI
  apply (le_div_iff₀ (by linarith : 0<1-(Fintype.card I:ℝ)*ε)).mpr
  simpa only [mul_comm,templateLaw,samplingError] using hs

theorem common_score (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ε η : ℝ} (hε : 0<ε) (hk : (Fintype.card I:ℝ)*ε<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) :
    (avg (templates π (templateLaw (I := I) π h))
      (fun θ => VP (slice π (templateLaw π h) θ) bit)+VQ π bit)/80000 ≤
    avg (templates π (templateLaw (I := I) π h))
      (fun θ => DP (slice π (templateLaw π h) θ) bit y)+DQ π bit x+
    12*(event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y+
      samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ε)+8*η) := by
  let ν := posteriorState π h x
  let Y : (I → H) → Finset (A×B) := Candidates ν ε
  choose W U hw hW hU hi hs using fun θ => witnesses (Y θ)
  let G : Q → (I → H) → Prop := fun q θ => ¬Failure (historyLaw π h q) ν ε (η^2) θ
  have hm (q : Q) (θ : I → H) (hg : G q θ) :
      1-3*η^2≤event (mix (historyLaw π h q) ν) (fun s => s∈U θ) := by
    apply witnesses_mass _ (W θ) (U θ) (sq_nonneg η) (hW θ) (hi θ)
    intro w hww
    by_contra hn
    exact hg ⟨w,hw θ hww,lt_of_not_ge hn⟩
  have ht := actual_transfer π h x hμ hκ (templateLaw (I := I) π h) U hU G hη hη' hm
  let good : (I → H) → P → Q → Prop := fun θ p q =>
    Consistent (bit p q) (x p) (y q) ∧ y q∈Y θ ∧ G q θ ∧ x p∈U θ
  have hc := aggregate_score π (templateLaw (I := I) π h) bit x y Y U good hs (by
    intro θ p q hpq
    exact ⟨hpq.2.2.2,hpq.2.1,hpq.1⟩)
  have hb : avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => ¬good θ pq.1 pq.2))≤
      event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y+
      samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ε)+8*η := by
    have hu : ∀pq : P×Q,event (templateLaw (I := I) π h pq.2) (fun θ => ¬good θ pq.1 pq.2)≤
        (if ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2) then 1 else 0)+
        event (templateLaw (I := I) π h pq.2) (fun θ => y pq.2∉Y θ)+
        event (templateLaw (I := I) π h pq.2) (fun θ => ¬G pq.2 θ)+
        event (templateLaw (I := I) π h pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ) := by
      intro pq
      rw [← avg_ite,← avg_ite,← avg_ite,← avg_ite,← avg_const (templateLaw (I := I) π h pq.2)
        (if ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2) then 1 else 0),← avg_add,← avg_add,← avg_add]
      apply avg_mono
      intro θ
      simpa only [good] using bad_good_indicator (Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
        (y pq.2∈Y θ) (G pq.2 θ) (x pq.1∈U θ)
    have ha := avg_mono π hu
    rw [avg_add,avg_add,avg_add,avg_ite] at ha
    have hmiss := candidate_miss_mean (I := I) π h x y hε
    have hfail := failure_mean (I := I) π h x (ε := ε)
      (sq_pos_of_pos hη) (by nlinarith) hI hk
    have hf : avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => ¬G pq.2 θ))=
        avg π (fun pq => event (templateLaw (I := I) π h pq.2)
          (Failure (historyLaw π h pq.2) ν ε (η^2))) := by
      apply avg_congr; intro pq
      apply event_congr; intro θ; simp [G]
    rw [hf] at ha
    change avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => y pq.2∉Y θ))≤_ at hmiss
    linarith
  linarith
end
end PlanarUnitDistances.CommonTemplate

end OAI
