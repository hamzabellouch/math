import OAI.Geometry.UnitDistances.Preparation

namespace OAI

namespace PlanarUnitDistances.LocalProfiles
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore RareMoments ScoreBook LevelScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

def rareBit (B : Book D P Q H A) (s : D) := minority (RareRows.frequency B.graph (B.bit s))
def exceptional (B : Book D P Q H A) (s : D) (a : A×A) : Prop := RareScore.exceptional (rareBit B s) (B.label s) a

def X (B : Book D P Q H A) (s : D) (p : P) : ℝ :=
  if B.R s then ind (exceptional B s (B.point s p)) else 0

def signed (B : Book D P Q H A) (s : D) (p : P) : ℝ := sign (rareBit B s)*X B s p

def jfirst (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.center s a.1))
def jsecond (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.2) ∧ exceptional B s (B.center s a.1))
def jpoints (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.point s a.2.2))
def ifirst (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (¬CrossStructure.Consistent (B.bit s a.2.1 a.1) (B.point s a.2.1) (B.center s a.1))
def isecond (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (¬CrossStructure.Consistent (B.bit s a.2.2 a.1) (B.point s a.2.2) (B.center s a.1))
def bits (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  value (B.bit s a.2.1 a.1)-value (B.bit s a.2.2 a.1)

def error1 (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  (if B.C s then |bits B s a| else 0)+ind (¬B.C s ∧ ¬B.good s)+
  (if B.R s then 2*(jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) else 0)
def error2 (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  if B.R s then 2*(jpoints B s a+jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) else 0

lemma X_nonneg (B : Book D P Q H A) (s : D) (p : P) : 0 ≤ X B s p := by
  unfold X ind
  positivity
lemma error1_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error1 B s a := by
  unfold error1 jfirst jsecond ifirst isecond ind
  positivity
lemma error2_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error2 B s a := by
  unfold error2 jpoints jfirst jsecond ifirst isecond ind
  positivity

lemma residual (B : Book D P Q H A) (s : D) (a : Q×(P×P)) :
    |bits B s a-(signed B s a.2.1-signed B s a.2.2)| ≤ error1 B s a := by
  by_cases hc : B.C s
  · simp [error1,signed,X,Book.R,hc,ind]
  · by_cases hg : B.good s
    · have hr : B.R s := ⟨hc,hg⟩
      have he : error1 B s a = 2*(jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) := by
        simp only [error1,hc,hr,hg,ite_false,ite_true,not_true_eq_false,and_false,ind,zero_add]
      rw [he]
      unfold signed bits
      rw [show X B s a.2.1=ind (exceptional B s (B.point s a.2.1)) from ite_eq_left hr,
        show X B s a.2.2=ind (exceptional B s (B.point s a.2.2)) from ite_eq_left hr,←mul_sub]
      exact wedge_residual (rareBit B s) (B.bit s a.2.1 a.1) (B.bit s a.2.2 a.1)
        (B.label s) (B.point s a.2.1) (B.center s a.1) (B.point s a.2.2)
    · simp only [error1,signed,X,Book.R,hc,hg,not_false_eq_true,true_and,ite_true,ite_false,
        and_false,ind,mul_zero,sub_zero,zero_add,add_zero]
      cases h₁ : B.bit s a.2.1 a.1 <;> cases h₂ : B.bit s a.2.2 a.1 <;> norm_num [bits,value,h₁,h₂]

lemma size (B : Book D P Q H A) (s : D) (a : Q×(P×P)) :
    X B s a.2.1+X B s a.2.2-error2 B s a ≤ |bits B s a| := by
  by_cases h : B.R s
  · simp only [X,error2,h,ite_true]
    exact wedge_size (rareBit B s) (B.bit s a.2.1 a.1) (B.bit s a.2.2 a.1)
      (B.label s) (B.point s a.2.1) (B.center s a.1) (B.point s a.2.2)
  · simp [X,error2,h]
end
end PlanarUnitDistances.LocalProfiles

namespace PlanarUnitDistances.WedgeSummary
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore ScoreBook LevelScores LocalProfiles
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

def JW (B : Book D P Q H A) := cut B.levels B.R (fun s => RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s))

lemma first_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jfirst B s)=RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s) := by
  rw [show jfirst B s=(fun a => ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.center s a.1))) from rfl,
    WedgeLaw.first B.graph (fun p q => ind (exceptional B s (B.point s p) ∧ exceptional B s (B.center s q)))]
  rfl
lemma second_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jsecond B s)=RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s) := by
  rw [show jsecond B s=(fun a => ind (exceptional B s (B.point s a.2.2) ∧ exceptional B s (B.center s a.1))) from rfl,
    WedgeLaw.second B.graph (fun p q => ind (exceptional B s (B.point s p) ∧ exceptional B s (B.center s q)))]
  rfl
lemma point_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jpoints B s)=RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s) := by
  rw [WedgeLaw.average]
  rfl
lemma first_error (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (ifirst B s)=RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) := by
  rw [show ifirst B s=(fun a => ind (¬CrossStructure.Consistent (B.bit s a.2.1 a.1) (B.point s a.2.1) (B.center s a.1))) from rfl,
    WedgeLaw.first B.graph (fun p q => ind (¬CrossStructure.Consistent (B.bit s p q) (B.point s p) (B.center s q)))]
  rfl
lemma second_error (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (isecond B s)=RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) := by
  rw [show isecond B s=(fun a => ind (¬CrossStructure.Consistent (B.bit s a.2.2 a.1) (B.point s a.2.2) (B.center s a.1))) from rfl,
    WedgeLaw.second B.graph (fun p q => ind (¬CrossStructure.Consistent (B.bit s p q) (B.point s p) (B.center s q)))]
  rfl

lemma X_average (B : Book D P Q H A) :
    avg B.levels (fun s => avg (left B.graph) (X B s))=B.HP := by
  apply avg_congr
  intro s
  unfold LocalProfiles.X
  by_cases h : B.R s
  · simp only [h,ite_true]
    rfl
  · simp only [h,ite_false,avg_const]

lemma err1_at (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (error1 B s)=
      (if B.C s then VQ B.graph (B.bit s) else 0)+ind (¬B.C s ∧ ¬B.good s)+
      (if B.R s then 4*RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s)+
        4*RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) else 0) := by
  unfold error1
  simp only [avg_add,avg_const]
  have hc : avg (WedgeLaw.law B.graph) (fun a => if B.C s then |bits B s a| else 0)=
      if B.C s then VQ B.graph (B.bit s) else 0 := by
    by_cases h : B.C s
    · simp only [h,ite_true,bits]
      exact WedgeLaw.mismatch B.graph (B.bit s)
    · simp [h,avg_const]
  rw [hc]
  congr 1
  by_cases h : B.R s
  · simp only [h,ite_true,avg_smul,avg_add,first_joint,second_joint,first_error,second_error]
    ring
  · simp [h,avg_const]

lemma err2_at (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (error2 B s)=
      if B.R s then 2*RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s)+
        4*RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s)+
        4*RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) else 0 := by
  unfold error2
  by_cases h : B.R s
  · simp only [h,ite_true,avg_smul,avg_add,point_joint,first_joint,second_joint,first_error,second_error]
    ring
  · simp [h,avg_const]

lemma cut_error (B : Book D P Q H A) :
    cut B.levels B.R (fun s => RareLabels.error B.graph (B.bit s) (B.point s) (B.center s)) ≤ B.M := by
  apply avg_mono
  intro s
  by_cases h : B.R s
  · simp only [h,ite_true]
    exact le_rfl
  · simp only [h,ite_false]
    exact event_nonneg _ _

theorem residual_budget (B : Book D P Q H A) :
    avg B.levels (fun s => avg (WedgeLaw.law B.graph) (error1 B s)) ≤ B.CQ+B.WB+4*B.J+4*B.M := by
  simp_rw [err1_at]
  rw [avg_add,avg_add]
  change B.CQ+B.WB+cut B.levels B.R (fun s => _+_) ≤ _
  rw [cut_add,cut_smul,cut_smul]
  have h := cut_error B
  change _ ≤ B.M at h
  dsimp only [Book.J]
  linarith

theorem size_budget (B : Book D P Q H A) :
    avg B.levels (fun s => avg (WedgeLaw.law B.graph) (error2 B s)) ≤ 2*JW B+4*B.J+4*B.M := by
  simp_rw [err2_at]
  change cut B.levels B.R (fun s => _+_+_) ≤ _
  rw [cut_add,cut_add,cut_smul,cut_smul,cut_smul]
  have h := cut_error B
  dsimp only [JW,Book.J]
  linarith
end
end PlanarUnitDistances.WedgeSummary

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
noncomputable section

lemma bit_integral {l u a : ℝ} (hla : l ≤ a) (hau : a ≤ u) :
    (∫s in Icc l u,bit a s)=a-l := by
  have he : bit a = (Iio a).indicator (fun _ => (1:ℝ)) := by
    funext s
    simp [bit,Set.indicator]
  rw [he,integral_indicator_const (1:ℝ) measurableSet_Iio,
    measureReal_restrict_apply measurableSet_Iio]
  have hi : Iio a ∩ Icc l u=Ico l a := by
    ext s
    simp only [mem_inter_iff,mem_Iio,mem_Icc,mem_Ico]
    constructor
    · rintro ⟨hsa,hls,hsu⟩
      exact ⟨hls,hsa⟩
    · rintro ⟨hls,hsa⟩
      exact ⟨hsa,hls,hsa.le.trans hau⟩
  rw [hi,Real.volume_real_Ico]
  simp [smul_eq_mul,max_eq_left (sub_nonneg.mpr hla)]

lemma signed_bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hau : a ≤ u)
    (hlb : l ≤ b) (hbu : b ≤ u) :
    (∫s in Icc l u,bit a s-bit b s)=a-b := by
  rw [integral_sub (bit_integrableOn a l u) (bit_integrableOn b l u),
    bit_integral hla hau,bit_integral hlb hbu]
  ring
end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.ActualProfiles
open MeasureTheory Set FiniteLaw LevelSnapshot ScoreBook ActualScoreBook PlaceLevels
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

structure Input (K : Type*) (V P Q H : Type) [Field K] [NumberField K]
    [Fintype V] [Fintype P] [Fintype Q] where
  support : Finset K
  z : V → K
  w : V → K
  point : P → V
  center : Q → V
  shifts : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts
  graph : Law (P×Q)
  history : P → H
  epsilon : ℝ
  good : Data V (P×Q) → Prop
  label : Data V (P×Q) → (V → Bool)×(V → Bool)
  mass_pos : 0 < mass support

namespace Input
variable (G : Input K V P Q H)
def book : ActualBook V P Q H := make G.support G.z G.w G.point G.center G.shifts
  G.graph G.history G.epsilon G.good G.label G.mass_pos
def snap (a : Place K G.support×ℝ) := snapshot G.support G.z G.w
  (fun pq : P×Q => G.point pq.1) (fun pq : P×Q => G.center pq.2) G.shifts a
def threshold (v : Place K G.support) (p : P) (q : Q) :=
  -Real.log (av K v (G.z (G.point p)-G.z (G.center q)))
def profile (p : P) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v), LocalProfiles.signed G.book (G.snap (v,s)) p
def heightAt (p : P) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v), LocalProfiles.X G.book (G.snap (v,s)) p
def errorAt (i : Bool) (a : Q×(P×P)) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v),
    (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book (G.snap (v,s)) a

lemma integral (F : Data V (P×Q) → ℝ) :
    Integrable (fun a => F (G.snap a)) (LevelScale.measure G.support) :=
  integrable_value _ _ _ _ _ _ F
lemma piece (F : Data V (P×Q) → ℝ) (v : Place K G.support) :
    IntegrableOn (fun s => F (G.snap (v,s))) (Icc (-radius K G.support v) (radius K G.support v)) :=
  integrable_piece _ _ _ _ _ _ F _ _ _

lemma bits_eq (a : Q×(P×P)) (v : Place K G.support) (s : ℝ) :
    LocalProfiles.bits G.book (G.snap (v,s)) a=
      ThresholdProfiles.bit (G.threshold v a.2.1 a.1) s-
      ThresholdProfiles.bit (G.threshold v a.2.2 a.1) s := by
  simp only [LocalProfiles.bits,book,make,snap,snapshot,LevelStates.bit,
    WedgeProfiles.value,threshold,ThresholdProfiles.bit,decide_eq_true_eq]
  rfl

lemma height_nonneg (p : P) (v : Place K G.support) : 0 ≤ G.heightAt p v :=
  integral_nonneg (fun _ => LocalProfiles.X_nonneg _ _ _)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) (v : Place K G.support) : 0 ≤ G.errorAt i a v := by
  apply integral_nonneg
  intro s
  cases i
  · exact LocalProfiles.error2_nonneg _ _ _
  · exact LocalProfiles.error1_nonneg _ _ _

theorem residual (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    |G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-
      (G.profile a.2.1 v-G.profile a.2.2 v)| ≤ G.errorAt true a v := by
  have hi := G.piece (fun d => LocalProfiles.bits G.book d a) v
  have h₁i := G.piece (fun d => LocalProfiles.signed G.book d a.2.1) v
  have h₂i := G.piece (fun d => LocalProfiles.signed G.book d a.2.2) v
  have he := G.piece (fun d => LocalProfiles.error1 G.book d a) v
  have h := integral_mono (hi.sub (h₁i.sub h₂i)).abs he
    (fun s => LocalProfiles.residual G.book (G.snap (v,s)) a)
  have hh := abs_integral_le_integral_abs (f := fun s =>
    LocalProfiles.bits G.book (G.snap (v,s)) a-
      (LocalProfiles.signed G.book (G.snap (v,s)) a.2.1-
        LocalProfiles.signed G.book (G.snap (v,s)) a.2.2))
    (μ := volume.restrict (Icc (-radius K G.support v) (radius K G.support v)))
  have hr₁ := threshold_in_range K h₁ v
  have hr₂ := threshold_in_range K h₂ v
  have ht : (∫s in Icc (-radius K G.support v) (radius K G.support v),
      LocalProfiles.bits G.book (G.snap (v,s)) a)=G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1 := by
    simp_rw [G.bits_eq]
    exact ThresholdProfiles.signed_bit_sub_integral hr₁.1 hr₁.2 hr₂.1 hr₂.2
  have ie := integral_sub hi (h₁i.sub h₂i)
  have ie' := integral_sub h₁i h₂i
  simp only [Pi.sub_apply] at ie ie'
  rw [ie,ie',ht] at hh
  exact hh.trans h

theorem size (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    G.heightAt a.2.1 v+G.heightAt a.2.2 v-G.errorAt false a v ≤
      |G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1| := by
  have hi := G.piece (fun d => LocalProfiles.bits G.book d a) v
  have h₁i := G.piece (fun d => LocalProfiles.X G.book d a.2.1) v
  have h₂i := G.piece (fun d => LocalProfiles.X G.book d a.2.2) v
  have he := G.piece (fun d => LocalProfiles.error2 G.book d a) v
  have h := integral_mono ((h₁i.add h₂i).sub he) hi.abs
    (fun s => LocalProfiles.size G.book (G.snap (v,s)) a)
  have ie := integral_sub (h₁i.add h₂i) he
  have ie' := integral_add h₁i h₂i
  simp only [Pi.sub_apply,Pi.add_apply] at h ie ie'
  rw [ie,ie'] at h
  have hr₁ := threshold_in_range K h₁ v
  have hr₂ := threshold_in_range K h₂ v
  have ht : (∫s in Icc (-radius K G.support v) (radius K G.support v),
      |LocalProfiles.bits G.book (G.snap (v,s)) a|)=|G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1| := by
    simp_rw [G.bits_eq]
    exact ThresholdProfiles.bit_sub_integral hr₁.1 hr₁.2 hr₂.1 hr₂.2
  rw [ht] at h
  exact h
end Input
end
end PlanarUnitDistances.ActualProfiles

namespace PlanarUnitDistances.SamplingDecay
open Filter CommonTemplate
noncomputable section
lemma limit {α : ℝ} (ha : 0 < α) (ha' : α < 1) :
    Tendsto (fun n => samplingError n α) atTop (nhds 0) := by
  have hr : 0 < 1-α := by linarith
  have hr' : 1-α < 1 := by linarith
  have hs : 0 < 1-α/2 := by linarith
  have hs' : 1-α/2 < 1 := by linarith
  have h0 : Tendsto (fun n : ℕ => (n:ℝ)^2*(1-α)^(n-2)) atTop (nhds 0) := by
    have hh := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.le hr').div_const ((1-α)^2)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [div_eq_iff (pow_ne_zero 2 hr.ne')]
    rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn]
  have h1 : Tendsto (fun n : ℕ => (1-α/2)^(n-1)) atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs').div_const (1-α/2)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [div_eq_iff hs.ne',←pow_succ,Nat.sub_add_cancel hn]
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs'
  simpa only [samplingError,mul_zero,add_zero] using (h0.add (h1.const_mul 2)).add (h2.const_mul (2/α))
end
end PlanarUnitDistances.SamplingDecay

namespace PlanarUnitDistances.BudgetParameters
open Filter CommonTemplate
noncomputable section

def vanishing (n : ℕ) : ℝ := 1/((n:ℝ)+1)
lemma vanishing_pos (n : ℕ) : 0 < vanishing n := by unfold vanishing; positivity
lemma vanishing_limit : Tendsto vanishing atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ)))

structure Params where
  epsilon : ℝ
  delta : ℝ
  eta : ℝ
  d : ℝ
  k : ℕ
  m : ℕ
  epsilon_pos : 0 < epsilon
  epsilon_lt : epsilon < 1/2
  delta_pos : 0 < delta
  eta_pos : 0 < eta
  eta_lt : eta < 1/2
  d_pos : 0 < d
  k_pos : 0 < k
  m_pos : 0 < m

def Params.zeta (a : Params) : ℝ := 1/(2*a.k)
lemma Params.zeta_pos (a : Params) : 0 < a.zeta := by
  have hk : (0:ℝ) < a.k := by exact_mod_cast a.k_pos
  unfold Params.zeta
  positivity
lemma Params.k_zeta (a : Params) : (a.k:ℝ)*a.zeta=1/2 := by
  have hk : (a.k:ℝ)≠0 := by exact_mod_cast a.k_pos.ne'
  unfold Params.zeta
  field_simp

def joint (C γ η ε ξ : ℝ) : ℝ := ((C*(ε+ε)/γ)^η+ξ)/γ

def leading (a : Params) (C γ η : ℝ) : ℝ :=
  8*joint C γ η a.epsilon 0*C+
    (96*a.eta+20*a.delta+24*samplingError a.k (a.eta^2)+
      (12*(a.k:ℝ)/a.zeta+20/a.delta)*4/(a.m:ℝ))/a.epsilon

def wedge (a : Params) (C γ η : ℝ) : ℝ :=
  (a.d+joint C γ η a.epsilon 0/Real.sqrt a.d)*C

theorem exists_small {C γ η s₀ ρ : ℝ} (_hC : 0 < C) (_hγ : 0 < γ)
    (hη : 0 < η) (hs : 0 < s₀) (hρ : 0 < ρ) :
    ∃a : Params, a.epsilon+a.epsilon ≤ s₀ ∧ leading a C γ η < ρ ∧ wedge a C γ η < ρ := by
  have hdlim : Tendsto (fun n => vanishing n*C) atTop (nhds 0) := by
    simpa only [zero_mul] using vanishing_limit.mul_const C
  obtain ⟨nd,hnd⟩ := (hdlim.eventually_lt_const (by linarith : (0:ℝ) < ρ/4)).exists
  let d := vanishing nd
  have hd : 0 < d := vanishing_pos nd
  have hq : Tendsto (fun n => joint C γ η (vanishing n) 0) atTop (nhds 0) := by
    have hh : Tendsto (fun n => C*(vanishing n+vanishing n)/γ) atTop (nhds 0) := by
      simpa only [add_zero,mul_zero,zero_div] using (vanishing_limit.add vanishing_limit).const_mul C |>.div_const γ
    simpa only [joint,add_zero,zero_div] using (hh.rpow_const_nhds_zero hη).div_const γ
  have hjlim : Tendsto (fun n => 8*joint C γ η (vanishing n) 0*C) atTop (nhds 0) := by
    simpa only [zero_mul,mul_zero] using (hq.const_mul 8).mul_const C
  have hwlim : Tendsto (fun n => joint C γ η (vanishing n) 0/Real.sqrt d*C) atTop (nhds 0) := by
    simpa only [zero_mul,zero_div] using (hq.div_const (Real.sqrt d)).mul_const C
  have helim : Tendsto (fun n => vanishing n+vanishing n) atTop (nhds 0) := by
    simpa only [zero_add] using vanishing_limit.add vanishing_limit
  obtain ⟨ne,hne0,hne1,hne2,hne3⟩ :=
    ((vanishing_limit.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).and
      ((helim.eventually_le_const hs).and
        ((hjlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8)).and
          (hwlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/4))))).exists
  let ε := vanishing ne
  have he : 0 < ε := vanishing_pos ne
  have halim : Tendsto (fun n => 96*vanishing n/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using (vanishing_limit.const_mul 96).div_const ε
  obtain ⟨na,hna0,hna1⟩ := ((vanishing_limit.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).and
    (halim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let a := vanishing na
  have ha : 0 < a := vanishing_pos na
  have hblim : Tendsto (fun n => 20*vanishing n/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using (vanishing_limit.const_mul 20).div_const ε
  obtain ⟨nb,hnb⟩ := (hblim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8)).exists
  let b := vanishing nb
  have hb : 0 < b := vanishing_pos nb
  have hklim : Tendsto (fun n => 24*samplingError n (a^2)/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using ((SamplingDecay.limit (sq_pos_of_pos ha)
      (by dsimp [a] at *; nlinarith [vanishing_pos na])).const_mul 24).div_const ε
  obtain ⟨k,hk,hke⟩ := ((eventually_gt_atTop 0).and
    (hklim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let ζ : ℝ := 1/(2*k)
  have hmlim : Tendsto (fun m : ℕ => (12*(k:ℝ)/ζ+20/b)*4/(m:ℝ)/ε) atTop (nhds 0) := by
    simpa only [zero_div] using (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R:=ℝ))).div_const ε
  obtain ⟨m,hm,hme⟩ := ((eventually_gt_atTop 0).and
    (hmlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let p : Params := ⟨ε,b,a,d,k,m,he,hne0,hb,ha,hna0,hd,hk,hm⟩
  refine ⟨p,hne1,?_,?_⟩
  · change 8*joint C γ η ε 0*C+
      (96*a+20*b+24*samplingError k (a^2)+(12*(k:ℝ)/ζ+20/b)*4/(m:ℝ))/ε < ρ
    rw [add_div,add_div,add_div]
    linarith
  · change (d+joint C γ η ε 0/Real.sqrt d)*C < ρ
    rw [add_mul]
    linarith
end
end PlanarUnitDistances.BudgetParameters

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)
def capacity : ℕ := a.m^(2*a.k)
def length : ℕ := LogHistory.length (capacity a) (s.t i)
lemma capacity_pos : 0 < capacity a := pow_pos a.m_pos _
lemma length_pos : 0 < length s a i := LogHistory.length_pos _ _
structure Realization where
  depth : ℕ
  depth_lt : depth < length s a i
  mass_pos : 0 < mass (model s i).support
  shifts : ((model s i).field →ₐ[ℚ] ℂ) → StateConsistency.Shifts
  history : s.P i → FiniteInformation.History (Fin a.m×Fin a.m) depth
  label : Data (s.P i⊕s.Q i) (s.P i×s.Q i) →
    ((s.P i⊕s.Q i) → Bool)×((s.P i⊕s.Q i) → Bool)

variable {s a i}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
@[instance_reducible] def labelFintype (V : Type) [Fintype V] : Fintype (V→Bool) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
@[instance_reducible] def snapshotFintype (V P Q : Type) [Fintype V] [Fintype P] [Fintype Q] : Fintype (Data V (P×Q)) := inferInstance
local instance : Fintype (Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
def Realization.good (_R : Realization s a i) (d : Data (s.P i⊕s.Q i) (s.P i×s.Q i)) : Prop :=
  error (graph s i) (fun p q => d.1 (p,q)) (fun p => d.2 (.inl p))
    (fun q => d.2 (.inr q)) ≤ a.epsilon

def Realization.input (R : Realization s a i) : ActualProfiles.Input (model s i).field
    (s.P i⊕s.Q i) (s.P i) (s.Q i) (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) where
  support := (model s i).support
  z := (model s i).z
  w := (model s i).w
  point := Sum.inl
  center := Sum.inr
  shifts := R.shifts
  graph := graph s i
  history := R.history
  epsilon := a.epsilon
  good := R.good
  label := R.label
  mass_pos := R.mass_pos

def Realization.book (R : Realization s a i) : ActualBook (s.P i⊕s.Q i) (s.P i) (s.Q i)
    (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) := R.input.book

def Realization.fractional (R : Realization s a i) : Prop :=
  ∀σ,StateConsistency.Fractional (R.shifts σ)
def Realization.scale_eq (R : Realization s a i) : Prop :=
  mass (model s i).support*R.book.S=scale s i
def Realization.mistake_bound (R : Realization s a i) : Prop :=
  mass (model s i).support*R.book.M ≤ 2*Real.log 2+4
def Realization.history_bound (R : Realization s a i) : Prop :=
  Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤ a.m^(2*length s a i)
def Realization.stable (R : Realization s a i) (L : ℝ) : Prop :=
  ∀d,minorityMass (graph s i) (R.book.bit d) ≤ L*(VP (graph s i) (R.book.bit d)+VQ (graph s i) (R.book.bit d))
def Realization.rare (R : Realization s a i) : Prop :=
  ∀d,R.book.R d → minorityMass (graph s i) (R.book.bit d) ≤ hp (graph s i) (R.book.bit d) (R.book.point d) (R.label d)+
    hq (graph s i) (R.book.bit d) (R.book.center d) (R.label d)+error (graph s i) (R.book.bit d) (R.book.point d) (R.book.center d)
def Realization.common_bound (R : Realization s a i) : Prop := R.book.WC ≤ R.book.S/a.epsilon
def Realization.bad_bound (R : Realization s a i) : Prop := R.book.WB ≤ R.book.M/a.epsilon
def Realization.height_bound (R : Realization s a i) (C : ℝ) : Prop := R.book.HP+R.book.HQ ≤ C*(R.book.S+R.book.M)
def Realization.joint_bound (R : Realization s a i) (C : ℝ) : Prop :=
  R.book.J ≤ joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(R.book.HP+R.book.HQ)
def Realization.wedge_bound (R : Realization s a i) (C : ℝ) : Prop :=
  WedgeSummary.JW R.book ≤ (a.d+joint C (27/50) (1/25) a.epsilon (s.ξ i)/Real.sqrt a.d)*R.book.HP
def Realization.prediction_bound (R : Realization s a i) : Prop :=
  R.book.EP ≤ R.book.M+R.book.WC*(4/(a.m:ℝ)+18*(IncidenceSequence.information (s.P i) (s.Q i)/(length s a i:ℝ))^(1/4:ℝ))
def Realization.Valid (R : Realization s a i) (C L : ℝ) : Prop :=
  R.fractional ∧ R.scale_eq ∧ R.mistake_bound ∧ R.history_bound ∧ R.stable L ∧ R.rare ∧
  R.common_bound ∧ R.bad_bound ∧ R.height_bound C ∧ R.joint_bound C ∧ R.wedge_bound C ∧ R.prediction_bound

theorem constants (s : Sequence) :
    ∃s₀ C L : ℝ,0 < s₀ ∧ 0 < C ∧ 0 < L ∧
      ∀a : Params,2*a.epsilon ≤ s₀ → ∀ᶠi in atTop,∃R : Realization s a i,R.Valid C L := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,h⟩ := ActualPrepared.constants
    (by norm_num : (0:ℝ) < 27/50) (by norm_num : (0:ℝ) < 1/25)
  refine ⟨s₀,C,L,hs,hC,hL,?_⟩
  intro a ha
  filter_upwards [s.error_limit.eventually_le_const hξ,(scale_limit s).eventually_gt_atTop 0] with i hi hscale
  let M := model s i
  have ht := h M.field (s.P i⊕s.Q i) (s.P i) (s.Q i) M.support M.z M.w
    Sum.inl Sum.inr (graph s i)
    (GeometricLaw.counting (s.P i) (GeometricLaw.card_pos _ _ (s.good i).positive).1)
    (GeometricLaw.counting (s.Q i) (GeometricLaw.card_pos _ _ (s.good i).positive).2)
    (fun p q hp => M.unit_identity p q (support s i p q hp)) (positive s i)
    (fun p => by
      rw [graph,GeometricLaw.left_eq]
      simpa only [GeometricLaw.counting,mul_one_div] using (s.good i).atomP p p.property)
    (fun q => by
      rw [graph,GeometricLaw.right_eq]
      simpa only [GeometricLaw.counting,mul_one_div] using (s.good i).atomQ q q.property)
    (s.ξ i) (s.good i).error_nonneg hi
    (GeometricLaw.expansion _ _ (s.good i).positive (s.good i).expansion)
    a.epsilon a.epsilon a.d a.epsilon_pos a.epsilon_pos a.d_pos (by linarith) hscale
    a.m (length s a i) a.m_pos (length_pos s a i)
  obtain ⟨hm,u,n,hn,g,l,hfrac,hS,hM,hcard,hstable,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := ht
  let R : Realization s a i := ⟨n,hn,hm,u,g,l⟩
  have hR : R.Valid C L := by
    as_aux_lemma =>
      refine ⟨hfrac,hS,hM,hcard,hstable,hrare,hWC,hWB,hH,hJ,hW,?_⟩
      have he := information_eq s i
      dsimp only [BoundedScaleFinite.information] at he
      rw [he] at hEP
      exact hEP
  exact ⟨R,hR⟩
end
end PlanarUnitDistances.IncidenceBook

namespace PlanarUnitDistances.BookEnvelope
open Filter FiniteLaw ScoreBook BookCoercivity BudgetParameters
open scoped Classical
noncomputable section

variable (a : Params) (C γ η ξ r : ℝ)
def height : ℝ := C*(1+r)
def j : ℝ := joint C γ η a.epsilon ξ/2*height C r
def pred : ℝ := r+(4/(a.m:ℝ)+18*r)/a.epsilon
def star : ℝ := r+2*r*(1/a.epsilon+height C r)
def prediction : ℝ := r+r/a.epsilon+r/a.epsilon
def common : ℝ := 12*r+(12*(a.k:ℝ)/a.zeta)*pred a r+
  (12*(CommonTemplate.samplingError a.k (a.eta^2)/(1-(a.k:ℝ)*a.zeta)+8*a.eta))/a.epsilon+
  8*j a C γ η ξ r+2*(r/a.epsilon)
def center : ℝ := 4*j a C γ η ξ r+6*r+r/a.epsilon
def point : ℝ := 4*j a C γ η ξ r+26*r+(20/a.delta)*pred a r+20*a.delta/a.epsilon+r/a.epsilon
def sc : ℝ := r+r/a.epsilon/2
def total : ℝ := common a C γ η ξ r+center a C γ η ξ r+point a C γ η ξ r+sc a r+
  3*star a C r+prediction a r

theorem total_limit (ξ r : ℕ → ℝ) (hξ : Tendsto ξ atTop (nhds 0))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun n => total a C γ η (ξ n) (r n)) atTop (nhds (leading a C γ η)) := by
  have hheight : Tendsto (fun n => height C (r n)) atTop (nhds (height C 0)) := by
    exact (tendsto_const_nhds.add hr).const_mul C
  have hjoint : Tendsto (fun n => joint C γ η a.epsilon (ξ n)) atTop
      (nhds (joint C γ η a.epsilon 0)) := by
    exact (tendsto_const_nhds.add hξ).div_const γ
  have hj : Tendsto (fun n => j a C γ η (ξ n) (r n)) atTop (nhds (j a C γ η 0 0)) :=
    (hjoint.div_const 2).mul hheight
  have hp : Tendsto (fun n => pred a (r n)) atTop (nhds (pred a 0)) :=
    hr.add ((tendsto_const_nhds.add (hr.const_mul 18)).div_const a.epsilon)
  have hs : Tendsto (fun n => star a C (r n)) atTop (nhds (star a C 0)) :=
    hr.add ((hr.const_mul 2).mul (tendsto_const_nhds.add hheight))
  have hpr : Tendsto (fun n => prediction a (r n)) atTop (nhds (prediction a 0)) :=
    (hr.add (hr.div_const a.epsilon)).add (hr.div_const a.epsilon)
  have hc : Tendsto (fun n => common a C γ η (ξ n) (r n)) atTop
      (nhds (common a C γ η 0 0)) :=
    ((((hr.const_mul 12).add (hp.const_mul (12*(a.k:ℝ)/a.zeta))).add
      tendsto_const_nhds).add (hj.const_mul 8)).add ((hr.div_const a.epsilon).const_mul 2)
  have hq : Tendsto (fun n => center a C γ η (ξ n) (r n)) atTop
      (nhds (center a C γ η 0 0)) :=
    ((hj.const_mul 4).add (hr.const_mul 6)).add (hr.div_const a.epsilon)
  have hpoint : Tendsto (fun n => point a C γ η (ξ n) (r n)) atTop
      (nhds (point a C γ η 0 0)) :=
    ((((hj.const_mul 4).add (hr.const_mul 26)).add (hp.const_mul (20/a.delta))).add
      tendsto_const_nhds).add (hr.div_const a.epsilon)
  have hsc : Tendsto (fun n => sc a (r n)) atTop (nhds (sc a 0)) :=
    hr.add ((hr.div_const a.epsilon).div_const 2)
  have hh : Tendsto (fun n => total a C γ η (ξ n) (r n)) atTop (nhds (total a C γ η 0 0)) :=
    ((((hc.add hq).add hpoint).add hsc).add (hs.const_mul 3)).add hpr
  convert hh using 1
  unfold total common center point sc star prediction pred j height leading joint
  rw [a.k_zeta]
  ring_nf

lemma sampling_nonneg : 0 ≤ CommonTemplate.samplingError a.k (a.eta^2) := by
  have h0 : 0 ≤ 1-a.eta^2 := by nlinarith [a.eta_pos,a.eta_lt]
  have h1 : 0 ≤ 1-a.eta^2/2 := by nlinarith [a.eta_pos,a.eta_lt]
  unfold CommonTemplate.samplingError
  positivity

variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]

omit [Fintype H] in
theorem bounds (B : Book D P Q H A) (hC : 0 ≤ C) (_hγ : 0 < γ) (_hξ : 0 ≤ ξ) (hr : 0 ≤ r)
    (hM : B.M ≤ r*B.S) (hWC : B.WC ≤ (1/a.epsilon)*B.S)
    (hWB : B.WB ≤ (r/a.epsilon)*B.S) (hJ : B.J ≤ j a C γ η ξ r*B.S)
    (hEP : B.EP ≤ pred a r*B.S) :
    loss (I:=Fin a.k) B a.zeta a.eta a.delta
      (star a C r*B.S) (star a C r*B.S) (star a C r*B.S) (prediction a r*B.S) ≤
        total a C γ η ξ r*B.S := by
  obtain ⟨hS,hM0,hP,hQ,hCP,hCQ,hJ0,hWC0,hWB0⟩ := B.nonneg
  have hEP0 : 0 ≤ B.EP := by
    unfold Book.EP
    apply cut_nonneg
    intro s
    unfold CommonTemplate.predictionError
    apply avg_nonneg
    intro pq
    exact sub_nonneg.mpr (event_le_one _ _)
  have hz := a.zeta_pos
  have he := a.epsilon_pos
  have hd := a.delta_pos
  have ha := a.eta_pos
  have hsample := sampling_nonneg a
  have hk : 0 < 1-(a.k:ℝ)*a.zeta := by rw [a.k_zeta]; norm_num
  have hc0 : 0 ≤ commonLoss (I:=Fin a.k) B a.zeta a.eta := by
    unfold commonLoss
    simp only [Fintype.card_fin]
    positivity
  have hq0 : 0 ≤ centerLoss B := by unfold centerLoss; positivity
  have hp0 : 0 ≤ pointLoss B a.delta := by unfold pointLoss; positivity
  have hs0 : 0 ≤ scaleLoss B := by unfold scaleLoss; positivity
  have hst : 0 ≤ star a C r := by unfold star height; positivity
  have hpr : 0 ≤ prediction a r := by unfold prediction; positivity
  have hc : commonLoss (I:=Fin a.k) B a.zeta a.eta ≤ common a C γ η ξ r*B.S := by
    unfold commonLoss common
    simp only [Fintype.card_fin]
    calc
      _ ≤ 12*(r*B.S)+(12*(a.k:ℝ)/a.zeta)*(pred a r*B.S)+
          (12*(CommonTemplate.samplingError a.k (a.eta^2)/(1-(a.k:ℝ)*a.zeta)+8*a.eta))*((1/a.epsilon)*B.S)+
          8*(j a C γ η ξ r*B.S)+2*((r/a.epsilon)*B.S) := by gcongr
      _ = _ := by ring
  have hq : centerLoss B ≤ center a C γ η ξ r*B.S := by
    unfold centerLoss center
    calc
      _ ≤ 4*(j a C γ η ξ r*B.S)+6*(r*B.S)+(r/a.epsilon)*B.S := by gcongr
      _ = _ := by ring
  have hp : pointLoss B a.delta ≤ point a C γ η ξ r*B.S := by
    unfold pointLoss point
    calc
      _ ≤ 4*(j a C γ η ξ r*B.S)+26*(r*B.S)+(20/a.delta)*(pred a r*B.S)+
        (20*a.delta)*((1/a.epsilon)*B.S)+(r/a.epsilon)*B.S := by gcongr
      _ = _ := by ring
  have hs : scaleLoss B ≤ sc a r*B.S := by
    unfold scaleLoss sc
    calc
      _ ≤ r*B.S+((r/a.epsilon)*B.S)/2 := by gcongr
      _ = _ := by ring
  unfold loss total
  rw [abs_of_nonneg hc0,abs_of_nonneg hq0,abs_of_nonneg hp0,abs_of_nonneg hs0,
    abs_of_nonneg (mul_nonneg hst hS),abs_of_nonneg (mul_nonneg hpr hS)]
  linarith
end
end PlanarUnitDistances.BookEnvelope

namespace PlanarUnitDistances.CoercivityAll
open FiniteLaw ScoreBook FiniteStarCoupling RareMoments BookCoercivity
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q]
  [Fintype H] [Fintype A] [Fintype I]
theorem all (B : Book D P Q H A)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    {ζ η δ L eP eQ eT ePred : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) (hδ : 0<δ) (hL : 0 ≤ L)
    (hstable : ∀s,B.C s → RareLabels.minorityMass B.graph (B.bit s) ≤ L*(VP B.graph (B.bit s)+VQ B.graph (B.bit s)))
    (hrare : ∀s,¬B.C s → B.good s → RareLabels.minorityMass B.graph (B.bit s) ≤
      hp B.graph (B.bit s) (B.point s) (B.label s)+hq B.graph (B.bit s) (B.center s) (B.label s)+
        RareLabels.error B.graph (B.bit s) (B.point s) (B.center s))
    (hDP : B.DP ≤ B.CP/20000000+eP) (hDQ : B.DQ ≤ B.CQ/20000000+eQ)
    (hDT : Book.DT (I := I) B ≤ Book.CT (I := I) B/20000000+eT)
    (hT : B.T ≤ 2*B.HP+ePred) :
    B.CQ ≤ 250000*loss (I := I) B ζ η δ eP eQ eT ePred ∧
    B.HQ ≤ B.HP+130000*loss (I := I) B ζ η δ eP eQ eT ePred ∧
    B.S ≤ (400000*L+2)*B.HP+(23000000000*L+130001)*loss (I := I) B ζ η δ eP eQ eT ePred := by
  obtain ⟨hE,h0,h1,h2,h3,h4,h5,h6,h7⟩ := loss_bounds (I := I) B ζ η δ eP eQ eT ePred
  have hc := B.common_lower (I := I) hμ hκ hζ hk hI hη hη'
  have hq := B.center_lower
  have hp := B.point_lower hδ
  have hs := B.scale_lower L hstable hrare
  have hnn := B.nonneg
  have hct := B.CT_nonneg (I := I)
  dsimp only [commonLoss,centerLoss,pointLoss,scaleLoss] at h0 h1 h2 h3
  exact ScoreCoercivity.from_scores (S := B.S) (HP := B.HP) (HQ := B.HQ)
    (CP := B.CP) (CQ := B.CQ) (CT := Book.CT (I := I) B)
    (DP := B.DP) (DQ := B.DQ) (DT := Book.DT (I := I) B) (T := B.T) hE hnn.2.2.1 hct hL
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
end
end PlanarUnitDistances.CoercivityAll

end OAI
