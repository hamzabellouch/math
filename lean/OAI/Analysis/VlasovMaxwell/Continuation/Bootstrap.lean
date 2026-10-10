import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.BulkTestWeight
import OAI.Analysis.VlasovMaxwell.Population.BulkReceiverResidual

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma first_level_time {Q : ℝ → ℝ} {T R : ℝ}
    (hQ : ContinuousOn Q (Ico 0 T)) (hQ0 : Q 0 < R)
    (hex : ∃ t ∈ Ico 0 T, R ≤ Q t) :
    ∃ t ∈ Ioo 0 T, Q t=R ∧ ∀ s ∈ Ico 0 t, Q s<R := by
  obtain ⟨b,hb,hRb⟩ := hex
  have hsub : Icc (0 : ℝ) b ⊆ Ico 0 T := fun s hs => ⟨hs.1,hs.2.trans_lt hb.2⟩
  have hc := hQ.mono hsub
  obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc hb.1 hc ⟨hQ0.le,hRb⟩
  let S : Set ℝ := Icc 0 b ∩ Q ⁻¹' {R}
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn ⟨x,hx,hfx⟩ continuousOn_id
  have hfm : Q m=R := hm.2
  have hm0 : 0 < m := by
    apply lt_of_le_of_ne hm.1.1
    intro he
    rw [← he] at hfm
    linarith
  refine ⟨m,⟨hm0,hm.1.2.trans_lt hb.2⟩,hfm,?_⟩
  intro s hs
  by_contra hn
  have hQs : R ≤ Q s := le_of_not_gt hn
  obtain ⟨y,hy,hey⟩ := intermediate_value_Icc hs.1
    (hc.mono (Icc_subset_Icc_right (hs.2.le.trans hm.1.2))) ⟨hQ0.le,hQs⟩
  have hyS : y ∈ S := ⟨⟨hy.1,hy.2.trans (hs.2.le.trans hm.1.2)⟩,hey⟩
  have hms : m ≤ s := (hmin hyS).trans hy.2
  exact (not_le_of_gt hs.2) hms

lemma last_level_time {Q : ℝ → ℝ} {t R : ℝ} (ht : 0 ≤ t)
    (hQ : ContinuousOn Q (Icc 0 t)) (hQ0 : Q 0 < R) (hRt : R < Q t) :
    ∃ s ∈ Ico 0 t, Q s=R ∧ ∀ u ∈ Ioc s t, R<Q u := by
  obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc ht hQ ⟨hQ0.le,hRt.le⟩
  let S : Set ℝ := Icc 0 t ∩ Q ⁻¹' {R}
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨m,hm,hmax⟩ := hS.exists_isMaxOn ⟨x,hx,hfx⟩ continuousOn_id
  have hfm : Q m=R := hm.2
  have hmt : m<t := by
    apply lt_of_le_of_ne hm.1.2
    intro he
    rw [he] at hfm
    linarith
  refine ⟨m,⟨hm.1.1,hmt⟩,hfm,?_⟩
  intro u hu
  by_contra hn
  have hQu : Q u ≤ R := le_of_not_gt hn
  have hu0 : 0 ≤ u := hm.1.1.trans hu.1.le
  obtain ⟨y,hy,hey⟩ := intermediate_value_Icc hu.2
    (hQ.mono (Icc_subset_Icc_left hu0)) ⟨hQu,hRt.le⟩
  have hyS : y ∈ S := ⟨⟨hu0.trans hy.1,hy.2⟩,hey⟩
  have hum : u ≤ m := hy.1.trans (hmax hyS)
  exact (not_le_of_gt hu.1) hum

lemma first_level_bound {Q : ℝ → ℝ} {t R : ℝ} (hQt : Q t=R)
    (hfirst : ∀ s ∈ Ico 0 t, Q s<R) : ∀ s ∈ Icc 0 t, Q s≤R := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with he|he
  · simpa only [he,hQt] using (le_refl R)
  · exact (hfirst s ⟨hs.1,he⟩).le

lemma first_levels_strict {Q : ℝ → ℝ} {a b R S : ℝ}
    (_ha : 0 ≤ a) (hQa : Q a=R) (hQb : Q b=S) (hRS : R<S)
    (_hfirst : ∀ s ∈ Ico 0 b, Q s<S) (hfirst' : ∀ s ∈ Ico 0 a, Q s<R)
    (hb : 0 ≤ b) : a<b := by
  by_contra hn
  have hba := le_of_not_gt hn
  have h := first_level_bound hQa hfirst' b ⟨hb,hba⟩
  rw [hQb] at h
  linarith

def PopulationIncrement {α : Type*} (V : α → ℝ → Vec) (K : Set α)
    (T M A P₀ : ℝ) : Prop :=
  ∀ τ ∈ Ico 0 T, ∀ k : ℕ, P₀ ≤ (2 : ℝ)^k →
    (∀ t ∈ Icc 0 τ, ∀ z ∈ K, 1024*q (V z t) ≤ (2 : ℝ)^k) →
    ∀ z ∈ K, IncrementBootstrap (V z) τ M A (2^k) (Real.log (2+2^k))

theorem momentum_bounded_of_increment {α : Type*} {V : α → ℝ → Vec}
    {K : Set α} {Q : ℝ → ℝ} {T M A P₀ : ℝ}
    (hQ : ContinuousOn Q (Ico 0 T))
    (hV : ∀ z ∈ K, ContinuousOn (V z) (Ico 0 T))
    (hmax : ∀ t ∈ Ico 0 T, ∀ z ∈ K, q (V z t) ≤ Q t)
    (hattain : ∀ t ∈ Ico 0 T, ∃ z ∈ K, Q t=q (V z t))
    (hM : 0 < M) (hA : 0 < A) (H : PopulationIncrement V K T M A P₀) :
    ∃ C : ℝ, ∀ t ∈ Ico 0 T, ∀ z ∈ K, q (V z t) ≤ C := by
  classical
  by_contra hnb
  push Not at hnb
  have hunbdd : ∀ R : ℝ, ∃ t ∈ Ico 0 T, R ≤ Q t := by
    intro R
    obtain ⟨t,ht,z,hz,he⟩ := hnb R
    exact ⟨t,ht,he.le.trans (hmax t ht z hz)⟩
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (max (Q 0) P₀) (by norm_num : (1:ℝ)<2)
  let R : ℕ → ℝ := fun n => (2:ℝ)^(N+n)
  have hRpos (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hRN (n : ℕ) : (2:ℝ)^N ≤ R n := by
    dsimp [R]
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right N n)
  have hR0 (n : ℕ) : Q 0<R n :=
    ((le_max_left _ _).trans_lt hN).trans_le (hRN n)
  have hRP (n : ℕ) : P₀ ≤ 1024*R n := by
    have hP := ((le_max_right _ _).trans_lt hN).le.trans (hRN n)
    nlinarith [hRpos n]
  have hdouble (n : ℕ) : R (n+1)=2*R n := by
    dsimp [R]
    rw [← Nat.add_assoc,pow_succ]
    ring
  have htimes (n : ℕ) := first_level_time hQ (hR0 n) (hunbdd (R n))
  choose t ht he hfirst using htimes
  have htinc (n : ℕ) : t n<t (n+1) := by
    apply first_levels_strict (ht n).1.le (he n) (he (n+1)) _
      (hfirst (n+1)) (hfirst n) (ht (n+1)).1.le
    rw [hdouble]
    linarith [hRpos n]
  have hbounded (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 (t n)) : Q s≤R n :=
    first_level_bound (he n) (hfirst n) s hs
  have hlabels (n : ℕ) := hattain (t (n+1)) ⟨(ht (n+1)).1.le,(ht (n+1)).2⟩
  choose z hz hze using hlabels
  have hzenergy (n : ℕ) : q (V (z n) (t (n+1)))=R (n+1) :=
    (hze n).symm.trans (he (n+1))
  have hzero := (ht 0).1.trans (ht 0).2
  have hlast (n : ℕ) := last_level_time (ht (n+1)).1.le
    (((contDiff_q (k:=1)).continuous.comp_continuousOn (hV (z n) (hz n))).mono
      (show Icc (0:ℝ) (t (n+1)) ⊆ Ico 0 T from
        fun _ hs => ⟨hs.1,hs.2.trans_lt (ht (n+1)).2⟩))
    ((hmax 0 ⟨le_rfl,hzero⟩ (z n) (hz n)).trans_lt (hR0 n))
    (show R n<q (V (z n) (t (n+1))) from by rw [hzenergy,hdouble]; linarith [hRpos n])
  choose s hs hse hlast using hlast
  simp only [Function.comp_def] at hse hlast
  have hst (n : ℕ) : t n ≤ s n := by
    by_contra hn
    have hslt : s n<t n := lt_of_not_ge hn
    have hh := hfirst n (s n) ⟨(hs n).1,hslt⟩
    have hdom := hmax (s n) ⟨(hs n).1,(hs n).2.trans (ht (n+1)).2⟩ (z n) (hz n)
    rw [hse n] at hdom
    linarith
  let Δ : ℕ → ℝ := fun n => t (n+1)-s n
  apply no_bounded_doubling_times (t := t) (Δ := Δ) (N+1) hM hA
    (fun n => (ht n).2.le) (fun n => sub_nonneg.mpr (hs n).2.le)
    (fun n => by dsimp [Δ]; linarith [hst n])
  intro n
  have hp : (2:ℝ)^(10+(N+(n+1)))=1024*R (n+1) := by
    rw [pow_add]
    norm_num [R]
  have hprefix : ∀ u ∈ Icc 0 (t (n+1)), ∀ y ∈ K,
      1024*q (V y u) ≤ (2:ℝ)^(10+(N+(n+1))) := by
    intro u hu y hy
    rw [hp]
    exact mul_le_mul_of_nonneg_left
      ((hmax u ⟨hu.1,hu.2.trans_lt (ht (n+1)).2⟩ y hy).trans (hbounded (n+1) hu))
      (by norm_num)
  have hH := H (t (n+1)) ⟨(ht (n+1)).1.le,(ht (n+1)).2⟩
    (10+(N+(n+1))) (by rw [hp]; exact hRP (n+1)) hprefix (z n) (hz n)
  have hband : ∀ u ∈ Icc (s n) (t (n+1)),
      (2:ℝ)^(N+(n+1))/8 ≤ q (V (z n) u) ∧
        q (V (z n) u) ≤ 8*(2:ℝ)^(N+(n+1)) := by
    intro u hu
    have hu0 : 0≤u := (hs n).1.trans hu.1
    have hlo : R n≤q (V (z n) u) := by
      rcases eq_or_lt_of_le hu.1 with hh|hh
      · rw [← hh,hse]
      · exact (hlast n u ⟨hh,hu.2⟩).le
    have hup := (hmax u ⟨hu0,hu.2.trans_lt (ht (n+1)).2⟩ (z n) (hz n)).trans
      (hbounded (n+1) ⟨hu0,hu.2⟩)
    change R (n+1)/8 ≤ _ ∧ _ ≤ 8*R (n+1)
    rw [hdouble] at *
    constructor <;> linarith [hRpos n]
  have hi := hH (N+(n+1)) (s n) (t (n+1)) (hs n).1 (hs n).2.le le_rfl hband
  rw [hp] at hi
  have hlow : R (n+1)/2 ≤ ‖V (z n) (t (n+1))-V (z n) (s n)‖ := by
    have hh := q_lipschitz (V (z n) (s n)) (V (z n) (t (n+1)))
    rw [hzenergy,hse] at hh
    have heq : R (n+1)-R n=R (n+1)/2 := by rw [hdouble]; ring
    rw [heq,abs_of_pos (half_pos (hRpos (n+1)))] at hh
    exact hh
  have heq : M*(1024*R (n+1))*Real.sqrt (Δ n)+
      A*(Δ n)*((1024*R (n+1))^2*Real.log (2+1024*R (n+1))/R (n+1)) =
      R (n+1)*(1024*M*Real.sqrt (Δ n)+1024^2*A*(Δ n)*Real.log (2+1024*R (n+1))) := by
    field_simp
  change ‖V (z n) (t (n+1))-V (z n) (s n)‖ ≤
    M*(1024*R (n+1))*Real.sqrt (Δ n)+
      A*(Δ n)*((1024*R (n+1))^2*Real.log (2+1024*R (n+1))/R (n+1)) at hi
  rw [heq] at hi
  have hh := hlow.trans hi
  have hpR := hRpos (n+1)
  have hres : (1:ℝ)/2 ≤ 1024*M*Real.sqrt (Δ n)+1024^2*A*(Δ n)*Real.log (2+1024*R (n+1)) := by
    nlinarith
  simpa only [R, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres
end RVM
end

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def incrementBound (M A P L w I : ℝ) : ℝ :=
  M*P*Real.sqrt I+A*I*(P^2*L/w)

lemma incrementBound_nonneg {M A P L w I : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hI : 0≤I) :
    0≤ incrementBound M A P L w I := by unfold incrementBound; positivity

lemma incrementBound_mono {M A P L w I J : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hIJ : I≤J) :
    incrementBound M A P L w I≤ incrementBound M A P L w J := by
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIJ) (mul_nonneg hM hP))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIJ hA) (by positivity))

lemma continuous_incrementBound (M A P L w : ℝ) : Continuous (incrementBound M A P L w) := by
  unfold incrementBound
  fun_prop

lemma IncrementBootstrap.ramp_error {V K : ℝ→Vec} {T M A P L a b : ℝ} (n : ℕ)
    (H : IncrementBootstrap V T M A P L) (ha : 0≤a) (hab : a<b) (hb : b≤T)
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L)
    (hband : ∀t∈Icc a b,(2:ℝ)^n/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^n)
    (hV : ContinuousOn V (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt V (K t) t) :
    ‖(∫t in a..b,directionWeight a b ((b-a)/256) t • K t)-(V b-V a)‖≤
      2*incrementBound M A P L (2^n) ((b-a)/256) := by
  have hl : 0<(b-a)/256 := by linarith
  have hn : 0≤(2:ℝ)^n := by positivity
  apply directionWeight_signed_error hl (by linarith) hV hK hd
  · intro t ht
    have htab : t≤b := by linarith [ht.2]
    exact (H n a t ha ht.1 (htab.trans hb) (fun u hu=>hband u ⟨hu.1,hu.2.trans htab⟩)).trans
      (incrementBound_mono hM hA hP hL hn (by linarith [ht.2]))
  · intro t ht
    have hat : a≤t := by linarith [ht.1]
    rw [norm_sub_rev]
    exact (H n t b (ha.trans hat) ht.2 hb (fun u hu=>hband u ⟨hat.trans hu.1,hu.2⟩)).trans
      (incrementBound_mono hM hA hP hL hn (by linarith [ht.1]))

lemma supported_weight_integral_eq {a b T : ℝ} {ψ : ℝ→ℝ} {K : ℝ→Vec}
    (hab : a≤b) (ha : 0≤a) (hb : b≤T) (hout : ∀t∉Icc a b,ψ t=0) :
    (∫t in Ioo (0:ℝ) T,ψ t • K t)=∫t in a..b,ψ t • K t := by
  rw [restrict_Ioo_eq_restrict_Ioc,←integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Icc_subset_Icc ha hb) ?_)
  intro t ht
  rw [hout t ht.2,zero_smul]

lemma closure_coefficient_bound {C M A P L w I : ℝ}
    (_ : 0≤C) (_ : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hI : 0≤I)
    (hCM : 8*C≤M) (hCA : 16*C*M≤A) (hC2A : 256*C^2≤A) :
    C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w)+
      2*incrementBound M A P L w (I/256) ≤ incrementBound M A P L w I/4 := by
  have hs : Real.sqrt (I/256)=Real.sqrt I/16 := by rw [Real.sqrt_div hI]; norm_num
  have hCs : C*Real.sqrt A≤A/16 := by
    have h1 : 16*C≤Real.sqrt A := by nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A]
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg A)
    nlinarith [Real.sq_sqrt hA]
  have h1 : C+M/8≤M/4 := by linarith
  have h2 : C*(M+Real.sqrt A)+A/128≤A/4 := by linarith
  have hp := mul_le_mul_of_nonneg_right h1 (mul_nonneg hP (Real.sqrt_nonneg I))
  have hq := mul_le_mul_of_nonneg_right h2 (show 0≤I*(P^2*L/w) by positivity)
  unfold incrementBound
  rw [hs]
  simp only [div_eq_mul_inv] at hp hq ⊢
  nlinarith only [hp,hq]

lemma PhaseFlowOn.physical_cap_of_labels {d : Datum} {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : SmoothClassicalPrefix d s T)
    (hcap : ∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) :
    ∀t∈Icc 0 T,∀z : Phase,s.f (t,z)≠0→1024*q z.2≤P := by
  intro t ht z hz
  have hf0 : d.f₀ (inversePhase F.flow (t,z))≠0 := by
    rw [←hs.initial_f,←F.transport_inverse hs.energyPrefix.f_smooth hs.energyPrefix.vlasov ht]
    exact hz
  have hh := hcap t ht (inversePhase F.flow (t,z)) (subset_tsupport _ hf0)
  simpa only [F.flow_inversePhase ht] using hh

lemma Admissible.signed_increment_strict {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A : ℝ,32≤M ∧ 1≤A ∧ ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
      (∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀z∈tsupport d.f₀,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤T →
      (∀t∈Icc a b,(2:ℝ)^n/8≤q (F.flow z t).2 ∧ q (F.flow z t).2≤8*(2:ℝ)^n) →
      ‖(F.flow z b).2-(F.flow z a).2‖≤
        incrementBound M A P (Real.log (2+P)) (2^n) (b-a)/2 := by
  obtain ⟨C,hC,hbulk⟩ := hd.force_bulk_uniform T₀ 512 (by norm_num)
  let M := 32+8*C
  let A := 1+16*C*M+256*C^2
  have hM32 : 32≤M := by dsimp [M]; linarith
  have hM : 0≤M := by linarith
  have hA1 : 1≤A := by dsimp [A]; nlinarith [mul_nonneg hC hM, sq_nonneg C]
  have hA : 0≤A := by linarith
  have hCM : 8*C≤M := by dsimp [M]; linarith
  have hCA : 16*C*M≤A := by dsimp [A]; nlinarith [sq_nonneg C]
  have hC2 : 256*C^2≤A := by dsimp [A]; nlinarith [mul_nonneg hC hM, sq_nonneg C]
  refine ⟨M,A,hM32,hA1,?_⟩
  filter_upwards [hbulk M A (by linarith) hA1] with P hB
  intro hP hL s T F hs hT hTT hcap H z hz n a b ha hab hb hband
  let w : ℝ := 2^n
  let I := b-a
  let V := fun t=>(F.flow z t).2
  let K := prefixMomentumForce s F.flow T z
  have hw : 1≤w := one_le_pow₀ (by norm_num)
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hI0 : 0≤I := sub_nonneg.mpr hab
  have hnon : 0≤ incrementBound M A P (Real.log (2+P)) w I :=
    incrementBound_nonneg hM hA hP0.le hL0 hw0.le hI0
  have hqa := hband a ⟨le_rfl,hab⟩
  have hqb := hband b ⟨hab,le_rfl⟩
  have hwp : w≤P := by
    have hc := hcap a ⟨ha,hab.trans hb⟩ z hz
    dsimp [w]
    nlinarith [q_pos (F.flow z a).2]
  by_cases hlarge : 32*w≤ incrementBound M A P (Real.log (2+P)) w I
  · have hn := norm_sub_le (F.flow z b).2 (F.flow z a).2
    have hna := norm_lt_q (F.flow z a).2
    have hnb := norm_lt_q (F.flow z b).2
    change _≤ incrementBound M A P (Real.log (2+P)) w I/2
    dsimp [w] at hlarge
    linarith
  by_cases he : a=b
  · subst b
    simp only [sub_self,norm_zero,incrementBound,Real.sqrt_zero,mul_zero,zero_mul,add_zero,zero_div,le_refl]
  have hab' : a<b := lt_of_le_of_ne hab he
  have hI : 0<I := sub_pos.mpr hab'
  have hIP : I≤(w/P)^2 := by
    have hterm : M*P*Real.sqrt I≤ incrementBound M A P (Real.log (2+P)) w I :=
      le_add_of_nonneg_right (by positivity)
    have hlower : 32*(P*Real.sqrt I)≤M*P*Real.sqrt I := by
      nlinarith only [mul_le_mul_of_nonneg_right hM32 (mul_nonneg hP0.le (Real.sqrt_nonneg I))]
    have hr : Real.sqrt I≤w/P := (le_div_iff₀ hP0).mpr (by linarith [lt_of_not_ge hlarge])
    nlinarith [Real.sq_sqrt hI0,Real.sqrt_nonneg I,div_nonneg hw0.le hP0.le]
  have hI1 : I≤1 := by
    have hr := (div_le_one hP0).mpr hwp
    have hr0 := div_nonneg hw0.le hP0.le
    nlinarith
  have hsrc : ∀z',s.f (0,z')≠0→∀r∈Icc 0 T,q (F.flow z' r).2≤P := by
    intro z' hz' r hr
    have hz0 : d.f₀ z'≠0 := by rwa [←hs.initial_f]
    have hh := hcap r hr z' (subset_tsupport _ hz0)
    nlinarith [q_pos (F.flow z' r).2]
  let ψ := directionWeight a b (I/256)
  obtain ⟨hψ1,hout,hψd,hdout,hψT⟩ := directionWeight_test (a:=a) (b:=b) (ℓ:=I/256)
    (η:=1/256) (I:=I) (T:=T) (by norm_num) hI (by dsimp [I]; ring_nf; exact le_rfl)
    (by dsimp [I]; linarith) hb
  have hd' : ∀t∈Icc a b,|deriv ψ t|≤512/I := by simpa only [show 2/(1/256:ℝ)=512 by norm_num] using hψd
  have hmain := hB hP hL s T F hs hT hTT z a b I w hz ha hb hab hI hI1 le_rfl hw hwp hIP
    hsrc (F.physical_cap_of_labels hs hcap) hband H ψ _ (directionWeight_lipschitz a b (I/256)) hψ1 hout hd' hdout hψT
  have heq : (∫t in Ioo (0:ℝ) T,ψ t •
      (s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))))=
      ∫t in a..b,ψ t • K t := by
    rw [←supported_weight_integral_eq hab ha hb hout]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [ψ,K,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  rw [heq] at hmain
  have hm : ‖∫t in a..b,ψ t • K t‖≤C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain
  have hdV : ∀t∈Ioo a b,HasDerivAt V (K t) t := by
    intro t ht
    have htT : t∈Ioo 0 T := ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
    have hh : HasDerivWithinAt V (K t) (Icc 0 T) t := by
      change HasDerivWithinAt (fun r=>(F.flow z r).2)
        (prefixMomentumForce s F.flow T z t) (Icc 0 T) t
      rw [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self htT)]
      exact (F.ode z t (Ioo_subset_Icc_self htT)).snd
    exact hh.hasDerivAt (Icc_mem_nhds htT.1 htT.2)
  have he := (H z hz).ramp_error n ha hab' hb hM hA hP0.le hL0 hband
    ((F.continuousOn_time z).snd.mono (Icc_subset_Icc ha hb))
    (F.continuous_prefixMomentumForce hs.energyPrefix hT z).continuousOn hdV
  have hn := norm_sub_norm_le (V b-V a) (∫t in a..b,ψ t • K t)
  rw [norm_sub_rev (V b-V a) (∫t in a..b,ψ t • K t)] at hn
  have hc := closure_coefficient_bound hC hM hA hP0.le hL0 hw0.le hI0 hCM hCA hC2
  change _≤ incrementBound M A P (Real.log (2+P)) w I/2
  change ‖(∫t in a..b,ψ t • K t)-(V b-V a)‖≤2*incrementBound M A P (Real.log (2+P)) w (I/256) at he
  change ‖V b-V a‖≤_
  linarith

lemma signed_bootstrap_propagation {α : Type*} {V : α→ℝ→Vec} {K : Set α}
    {T M A P L C : ℝ} (hT : 0≤T) (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L) (hC : 0≤C)
    (hLip : ∀z∈K,∀a∈Icc 0 T,∀b∈Icc 0 T,‖V z b-V z a‖≤C*|b-a|)
    (hstrict : ∀τ∈Icc 0 T,(∀z∈K,IncrementBootstrap (V z) τ M A P L) →
      ∀z∈K,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤τ →
        (∀t∈Icc a b,(2:ℝ)^n/8≤q (V z t) ∧ q (V z t)≤8*(2:ℝ)^n) →
        ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)/2) :
    ∀z∈K,IncrementBootstrap (V z) T M A P L := by
  let H := fun τ=>∀z∈K,IncrementBootstrap (V z) τ M A P L
  let S := {τ : ℝ | τ∈Icc 0 T ∧ H τ}
  have hzero : (0:ℝ)∈S := by
    refine ⟨⟨le_rfl,hT⟩,?_⟩
    intro z hz n a b ha hab hb hband
    have he : a=b := by linarith
    rw [he]
    simp only [sub_self,norm_zero,Real.sqrt_zero,mul_zero,zero_mul,add_zero,le_refl]
  have hbdd : BddAbove S := ⟨T,fun τ hτ=>hτ.1.2⟩
  let τ := sSup S
  have hτ0 : 0≤τ := le_csSup hbdd hzero
  have hτT : τ≤T := csSup_le ⟨0,hzero⟩ (fun r hr=>hr.1.2)
  have hτ : τ∈Icc 0 T := ⟨hτ0,hτT⟩
  have hbound : H τ := by
    intro z hz n a b ha hab hb hband
    change ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)
    rcases hab.eq_or_lt with he|hab
    · rw [he]; simp [incrementBound]
    apply le_of_forall_pos_le_add
    intro ε hε
    let r := max a (b-ε/(C+1))
    have hden : 0<C+1 := by linarith
    have hrb : r<b := max_lt hab (by linarith [div_pos hε hden])
    have har : a≤r := le_max_left _ _
    have hr0 : 0≤r := ha.trans har
    obtain ⟨σ,hσ,hrσ⟩ := exists_lt_of_lt_csSup ⟨0,hzero⟩ (hrb.trans_le hb)
    have hpart := hσ.2 z hz n a r ha har hrσ.le (fun t ht=>hband t ⟨ht.1,ht.2.trans hrb.le⟩)
    change ‖V z r-V z a‖≤ incrementBound M A P L (2^n) (r-a) at hpart
    have hm := incrementBound_mono hM.le hA hP.le hL (show 0≤(2:ℝ)^n by positivity)
      (show r-a≤b-a by linarith)
    have hl := hLip z hz r ⟨hr0,hrb.le.trans (hb.trans hτT)⟩ b ⟨ha.trans hab.le,hb.trans hτT⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hrb.le)] at hl
    have hdiff : b-r≤ε/(C+1) := by have := le_max_right a (b-ε/(C+1)); dsimp [r]; linarith
    have hcost : C*(b-r)≤ε := by
      have hh := mul_le_mul_of_nonneg_left hdiff hC
      have he := (div_mul_cancel₀ ε (ne_of_gt hden))
      nlinarith [div_pos hε hden]
    have hn : ‖V z b-V z a‖≤‖V z b-V z r‖+‖V z r-V z a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  have hmem : τ∈S := ⟨hτ,hbound⟩
  by_cases he : τ=T
  · rwa [←he]
  have hτlt : τ<T := lt_of_le_of_ne hτT he
  let ℓ := (M*P/(C+1))^2
  have hden : 0<C+1 := by linarith
  have hMP : 0<M*P := mul_pos hM hP
  have hratio : 0<M*P/(C+1) := div_pos hMP hden
  have hℓ : 0<ℓ := sq_pos_of_pos hratio
  have hsℓ : Real.sqrt ℓ=M*P/(C+1) := Real.sqrt_sq hratio.le
  have hshort : ∀z∈K,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤T → b-a≤ℓ →
      ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a) := by
    intro z hz n a b ha hab hb hlen
    have hl := hLip z hz a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hl
    have hs : Real.sqrt (b-a)≤M*P/(C+1) := by simpa only [hsℓ] using Real.sqrt_le_sqrt hlen
    have hh := (le_div_iff₀ hden).mp hs
    have hprod := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg (b-a))
    have hsq := Real.sq_sqrt (sub_nonneg.mpr hab)
    have hrest : 0≤A*(b-a)*(P^2*L/(2:ℝ)^n) := by positivity
    unfold incrementBound
    nlinarith
  let δ := min ((T-τ)/2) (min (ℓ/2) (M*P*Real.sqrt ℓ/(2*(C+1))))
  have hδ : 0<δ := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hδT : δ≤(T-τ)/2 := min_le_left _ _
  have hδℓ : δ≤ℓ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδcost : δ≤M*P*Real.sqrt ℓ/(2*(C+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hnewT : τ+δ≤T := by linarith
  have hnew : H (τ+δ) := by
    intro z hz n a b ha hab hb hband
    change ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)
    by_cases hlen : b-a≤ℓ
    · exact hshort z hz n a b ha hab (hb.trans hnewT) hlen
    have hat : a<τ := by linarith
    by_cases hbt : b≤τ
    · exact hbound z hz n a b ha hab hbt hband
    have htb : τ≤b := (lt_of_not_ge hbt).le
    have hp := hstrict τ hτ hbound z hz n a τ ha hat.le le_rfl
      (fun t ht=>hband t ⟨ht.1,ht.2.trans htb⟩)
    have hm := incrementBound_mono hM.le hA hP.le hL (show 0≤(2:ℝ)^n by positivity)
      (show τ-a≤b-a by linarith)
    have hl := hLip z hz τ hτ b ⟨hτ0.trans htb,hb.trans hnewT⟩
    rw [abs_of_nonneg (sub_nonneg.mpr htb)] at hl
    have hs := Real.sqrt_le_sqrt (le_of_not_ge hlen)
    have hpos := Real.sqrt_nonneg ℓ
    have hc : C*(b-τ)≤M*P*Real.sqrt (b-a)/2 := by
      have hh := (le_div_iff₀ (by positivity : 0<2*(C+1))).mp hδcost
      have h1 := mul_le_mul_of_nonneg_left (show b-τ≤δ by linarith) hC
      have h2 := mul_le_mul_of_nonneg_left hs hMP.le
      nlinarith
    have hrest : 0≤A*(b-a)*(P^2*L/(2:ℝ)^n) := by positivity
    have hn : ‖V z b-V z a‖≤‖V z b-V z τ‖+‖V z τ-V z a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    dsimp [incrementBound] at hp hm ⊢
    linarith
  have hnewmem : τ+δ∈S := ⟨⟨by linarith,hnewT⟩,hnew⟩
  have hh : τ+δ≤τ := le_csSup hbdd hnewmem
  linarith

def PhaseFlowOn.restrict {E B : Field} {T τ : ℝ} (F : PhaseFlowOn E B T) (hτT : τ≤T) :
    PhaseFlowOn E B τ where
  flow := F.flow
  differential := F.differential
  initial := F.initial
  ode := fun z t ht=>(F.ode z t ⟨ht.1,ht.2.trans hτT⟩).mono (Icc_subset_Icc le_rfl hτT)
  label := fun z t ht=>F.label z t ⟨ht.1,ht.2.trans hτT⟩
  det_one := fun z t ht=>F.det_one z t ⟨ht.1,ht.2.trans hτT⟩
  joint := fun z t ht=>F.joint z t ⟨ht.1,ht.2.trans_le hτT⟩
  bijective := fun t ht=>F.bijective t ⟨ht.1,ht.2.trans hτT⟩

lemma SmoothClassicalPrefix.restrict {d : Datum} {s : Solution} {T τ : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hτT : τ≤T) : SmoothClassicalPrefix d s τ where
  f_smooth := hs.f_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  E_smooth := hs.E_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  B_smooth := hs.B_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  nonnegative := fun t ht=>hs.nonnegative t ⟨ht.1,ht.2.trans hτT⟩
  E_L2 := by
    obtain ⟨F₂,hF,hE⟩ := hs.E_L2
    exact ⟨F₂,hF.mono (Icc_subset_Icc le_rfl hτT),fun t ht=>hE t ⟨ht.1,ht.2.trans hτT⟩⟩
  B_L2 := by
    obtain ⟨F₂,hF,hB⟩ := hs.B_L2
    exact ⟨F₂,hF.mono (Icc_subset_Icc le_rfl hτT),fun t ht=>hB t ⟨ht.1,ht.2.trans hτT⟩⟩
  compact := by
    obtain ⟨K,hK,hk⟩ := hs.compact
    exact ⟨K,hK,fun t ht=>hk t ⟨ht.1,ht.2.trans hτT⟩⟩
  equations := fun t ht htτ=>hs.equations t ht (htτ.trans_le hτT)
  initial_f := hs.initial_f
  initial_E := hs.initial_E
  initial_B := hs.initial_B

lemma PhaseFlowOn.supported_momentum_lipschitz {d : Datum} {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hd : Admissible d) (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) :
    ∃C : ℝ,0≤C ∧ ∀z∈tsupport d.f₀,∀a∈Icc 0 T,∀b∈Icc 0 T,
      ‖(F.flow z b).2-(F.flow z a).2‖≤C*|b-a| := by
  have hα := F.continuous_prefixFlow hs.energyPrefix hT
  have hX : Continuous (fun p : ℝ×Phase=>(p.1,(prefixFlow F.flow T p.2 p.1).1)) := continuous_fst.prodMk hα.fst
  have hE := (continuous_prefixField hs.energyPrefix.E_smooth.continuousOn hT).comp hX
  have hB := (continuous_prefixField hs.energyPrefix.B_smooth.continuousOn hT).comp hX
  have hv := (contDiff_velocity (k:=1)).continuous.comp hα.snd
  have hc : Continuous (fun p : ℝ×Phase=>prefixMomentumForce s F.flow T p.2 p.1) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp (hv.prodMk hB))
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod hd.2.1).bddAbove_image hc.norm.continuousOn
  let C := max 0 R
  have hC : 0≤C := le_max_left _ _
  refine ⟨C,hC,?_⟩
  intro z hz a ha b hb
  have hLip : LipschitzOnWith ⟨C,hC⟩ (fun t=>(F.flow z t).2) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun t ht=>(F.ode z t ht).snd)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖(lorentzField s.E s.B (t,F.flow z t)).2‖≤C
    have hh := hR ⟨(t,z),⟨ht,hz⟩,rfl⟩
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq ht] at hh
    exact hh.trans (le_max_right _ _)
  have hh := hLip.dist_le_mul b hb a ha
  change ‖(F.flow z b).2-(F.flow z a).2‖≤C*‖b-a‖ at hh
  simpa only [Real.norm_eq_abs] using hh

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.uniform_signed_increment {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A P₀ : ℝ,32≤M ∧ 1≤A ∧ 1≤P₀ ∧
    ∀P : ℝ,P₀≤P →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
      (∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) →
      ∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P)) := by
  obtain ⟨M,A,hM,hA,hstrict⟩ := hd.signed_increment_strict T₀
  obtain ⟨P₁,hP₁⟩ := Filter.eventually_atTop.mp hstrict
  obtain ⟨P₂,hP₂⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (Filter.tendsto_atTop_add_const_left _ 2 tendsto_id)).eventually (eventually_ge_atTop 1))
  let P₀ := max 1 (max P₁ P₂)
  refine ⟨M,A,P₀,hM,hA,le_max_left _ _,?_⟩
  intro P hP s T F hs hT hTT hcap
  have hP1 : 1≤P := (le_max_left 1 _).trans hP
  have hlog : 1≤Real.log (2+P) := hP₂ P (((le_max_right P₁ P₂).trans (le_max_right 1 _)).trans hP)
  have hS := hP₁ P (((le_max_left P₁ P₂).trans (le_max_right 1 _)).trans hP)
  obtain ⟨C,hC,hLip⟩ := F.supported_momentum_lipschitz hd hs hT
  apply signed_bootstrap_propagation hT (by linarith) (by linarith)
    (by linarith) (by linarith) hC hLip
  intro τ hτ H z hz n a b ha hab hb hband
  exact hS hP1 hlog s τ (F.restrict hτ.2) (hs.restrict hτ.2) hτ.1 (hτ.2.trans hTT)
    (fun t ht=>hcap t ⟨ht.1,ht.2.trans hτ.2⟩) H z hz n a b ha hab hb hband

lemma Admissible.population_increment {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A P₀ : ℝ,0<M ∧ 0<A ∧ 1≤P₀ ∧
    ∀(s : Solution) (T : ℝ) (flow : Phase→ℝ→Phase),T≤T₀ →
      (∀τ∈Ico 0 T, SmoothClassicalPrefix d s τ ∧
        ∃ F : PhaseFlowOn s.E s.B τ,F.flow=flow) →
      PopulationIncrement (fun z t=>(flow z t).2) (tsupport d.f₀) T M A P₀ := by
  obtain ⟨M,A,P₀,hM,hA,hP₀,hU⟩ := hd.uniform_signed_increment T₀
  refine ⟨M,A,P₀,by linarith,by linarith,hP₀,?_⟩
  intro s T flow hTT hpref τ hτ k hk hcap
  obtain ⟨hs,F,hF⟩ := hpref τ hτ
  have hh := hU (2^k) hk s τ F hs hτ.1 (hτ.2.le.trans hTT)
  rw [hF] at hh
  exact hh hcap

end RVM

end

end OAI
