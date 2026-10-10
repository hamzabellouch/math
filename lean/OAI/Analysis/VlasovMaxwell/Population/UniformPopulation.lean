import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.Bootstrap

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

theorem uniform_population_bounded_of_increment {ι α : Type*}
    {V : ι → α → ℝ → Vec} {K : ι → Set α} {Q : ι → ℝ → ℝ}
    {T : ι → ℝ} {H M A P₀ Q₀ : ℝ}
    (hT : ∀ i, T i ≤ H) (hQ₀ : ∀ i, Q i 0 ≤ Q₀)
    (hQ : ∀ i, ContinuousOn (Q i) (Ico 0 (T i)))
    (hV : ∀ i z, z∈K i → ContinuousOn (V i z) (Ico 0 (T i)))
    (hmax : ∀ i t, t∈Ico 0 (T i) → ∀ z∈K i, q (V i z t) ≤ Q i t)
    (hattain : ∀ i t, t∈Ico 0 (T i) → ∃ z∈K i, Q i t=q (V i z t))
    (hM : 0 < M) (hA : 0 < A)
    (hincrement : ∀ i, PopulationIncrement (V i) (K i) (T i) M A P₀) :
    ∃ C : ℝ, ∀ i t, t∈Ico 0 (T i) → ∀ z∈K i, q (V i z t) ≤ C := by
  classical
  by_contra hnb
  push Not at hnb
  have hunbdd : ∀ R : ℝ, ∃ i t, t∈Ico 0 (T i) ∧ R ≤ Q i t := by
    intro R
    obtain ⟨i,t,ht,z,hz,he⟩ := hnb R
    exact ⟨i,t,ht,he.le.trans (hmax i t ht z hz)⟩
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (max Q₀ P₀) (by norm_num : (1:ℝ)<2)
  let R : ℕ → ℝ := fun n=>(2:ℝ)^(N+n)
  have hRpos (n : ℕ) : 0<R n := by dsimp only [R]; positivity
  have hRN (n : ℕ) : (2:ℝ)^N ≤ R n := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right N n)
  have hR0 (i : ι) (n : ℕ) : Q i 0<R n :=
    (hQ₀ i).trans_lt (((le_max_left _ _).trans_lt hN).trans_le (hRN n))
  have hRP (n : ℕ) : P₀ ≤ 1024*R n := by
    have hP := ((le_max_right _ _).trans_lt hN).le.trans (hRN n)
    nlinarith only [hP,hRpos n]
  have hdouble (n : ℕ) : R (n+1)=2*R n := by
    dsimp only [R]
    rw [←Nat.add_assoc,pow_succ]
    ring
  let S : ℕ → Set ℝ := fun n=>{t | ∃ i, t∈Ioo 0 (T i) ∧ Q i t=R n ∧
    ∀ u∈Ico 0 t,Q i u<R n}
  have hne (n : ℕ) : (S n).Nonempty := by
    obtain ⟨i,t,ht,he⟩ := hunbdd (R n)
    obtain ⟨r,hr,heq,hfirst⟩ := first_level_time (hQ i) (hR0 i n) ⟨t,ht,he⟩
    exact ⟨r,i,hr,heq,hfirst⟩
  have hbdd (n : ℕ) : BddBelow (S n) := by
    refine ⟨0,?_⟩
    rintro t ⟨i,ht,he,hfirst⟩
    exact ht.1.le
  let tinf : ℕ → ℝ := fun n=>sInf (S n)
  have htinf (n : ℕ) : tinf n ≤ H := by
    obtain ⟨t,ht⟩ := hne n
    have hh := csInf_le (hbdd n) ht
    rcases ht with ⟨i,hi,he,hfirst⟩
    exact hh.trans (hi.2.le.trans (hT i))
  let L := Real.log 1026+(N+1)*Real.log 2+Real.log 2
  have hL : 0 < L := by
    have h1 : 0 < Real.log 1026 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [L]
    positivity
  let c := min ((4*1024*M)^2)⁻¹ (4*1024^2*A*L)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  apply no_bounded_harmonic_gaps hc htinf
  intro n
  have hh : tinf n+c/(n+1) ≤ tinf (n+1) := by
    apply le_csInf (hne (n+1))
    rintro τ ⟨i,hτ,hbig,hfirst⟩
    have hτ' : τ∈Ico 0 (T i) := ⟨hτ.1.le,hτ.2⟩
    have hbounded {u : ℝ} (hu : u∈Icc 0 τ) : Q i u≤R (n+1) :=
      first_level_bound hbig hfirst u hu
    obtain ⟨tl,htl,htle,hfirstl⟩ := first_level_time (hQ i) (hR0 i n)
      ⟨τ,hτ',by rw [hbig,hdouble]; linarith only [hRpos n]⟩
    have hinf : tinf n≤tl := csInf_le (hbdd n) ⟨i,htl,htle,hfirstl⟩
    obtain ⟨z,hz,hze⟩ := hattain i τ hτ'
    have hzenergy : q (V i z τ)=R (n+1) := hze.symm.trans hbig
    have hzero : 0<T i := hτ.1.trans hτ.2
    obtain ⟨s,hs,hse,hlast⟩ := last_level_time hτ.1.le
      (((contDiff_q (k:=1)).continuous.comp_continuousOn (hV i z hz)).mono
        (show Icc (0:ℝ) τ⊆Ico 0 (T i) from fun _ hu=>⟨hu.1,hu.2.trans_lt hτ.2⟩))
      ((hmax i 0 ⟨le_rfl,hzero⟩ z hz).trans_lt (hR0 i n))
      (show R n<q (V i z τ) from by rw [hzenergy,hdouble]; linarith only [hRpos n])
    simp only [Function.comp_def] at hse hlast
    have hst : tl ≤ s := by
      by_contra hn
      have hslt : s < tl := lt_of_not_ge hn
      have hh := hfirstl s ⟨hs.1,hslt⟩
      have hdom := hmax i s ⟨hs.1,hs.2.trans hτ.2⟩ z hz
      rw [hse] at hdom
      linarith only [hh,hdom]
    let Δ := τ-s
    have hΔ : 0≤Δ := sub_nonneg.mpr hs.2.le
    have hp : (2:ℝ)^(10+(N+(n+1)))=1024*R (n+1) := by
      rw [pow_add]
      norm_num [R]
    have hprefix : ∀ u∈Icc 0 τ,∀ y∈K i,1024*q (V i y u)≤(2:ℝ)^(10+(N+(n+1))) := by
      intro u hu y hy
      rw [hp]
      exact mul_le_mul_of_nonneg_left
        ((hmax i u ⟨hu.1,hu.2.trans_lt hτ.2⟩ y hy).trans (hbounded hu)) (by norm_num)
    have hH := hincrement i τ hτ' (10+(N+(n+1))) (by rw [hp]; exact hRP (n+1)) hprefix z hz
    have hband : ∀ u∈Icc s τ,(2:ℝ)^(N+(n+1))/8≤q (V i z u) ∧
        q (V i z u)≤8*(2:ℝ)^(N+(n+1)) := by
      intro u hu
      have hu0 : 0≤u := hs.1.trans hu.1
      have hlo : R n≤q (V i z u) := by
        rcases eq_or_lt_of_le hu.1 with hh|hh
        · rw [←hh,hse]
        · exact (hlast u ⟨hh,hu.2⟩).le
      have hup := (hmax i u ⟨hu0,hu.2.trans_lt hτ.2⟩ z hz).trans (hbounded ⟨hu0,hu.2⟩)
      change R (n+1)/8≤_ ∧ _≤8*R (n+1)
      rw [hdouble] at *
      constructor <;> linarith only [hlo,hup,hRpos n]
    have hi := hH (N+(n+1)) s τ hs.1 hs.2.le le_rfl hband
    rw [hp] at hi
    have hlow : R (n+1)/2 ≤ ‖V i z τ-V i z s‖ := by
      have hh := q_lipschitz (V i z s) (V i z τ)
      rw [hzenergy,hse] at hh
      have heq : R (n+1)-R n=R (n+1)/2 := by rw [hdouble]; ring
      rw [heq,abs_of_pos (half_pos (hRpos (n+1)))] at hh
      exact hh
    have heq : M*(1024*R (n+1))*Real.sqrt Δ+
        A*Δ*((1024*R (n+1))^2*Real.log (2+1024*R (n+1))/R (n+1)) =
        R (n+1)*(1024*M*Real.sqrt Δ+1024^2*A*Δ*Real.log (2+1024*R (n+1))) := by
      field_simp
    change ‖V i z τ-V i z s‖ ≤ M*(1024*R (n+1))*Real.sqrt Δ+
      A*Δ*((1024*R (n+1))^2*Real.log (2+1024*R (n+1))/R (n+1)) at hi
    rw [heq] at hi
    have hres : (1:ℝ)/2≤1024*M*Real.sqrt Δ+1024^2*A*Δ*Real.log (2+1024*R (n+1)) := by
      have hh := hlow.trans hi
      have hpR := hRpos (n+1)
      nlinarith only [hh,hpR]
    have hlog : Real.log (2+1024*R (n+1))≤L*(n+1) := by
      simpa only [R,L,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.cast_add,Nat.cast_one]
        using doubling_log_bound (N+1) n
    have hdelay : c/(n+1)≤Δ := by
      apply doubling_interval_lower_bound hM hA hL hΔ
      exact hres.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg (by positivity) hA.le) hΔ)))
    dsimp only [Δ] at hdelay
    linarith only [hdelay,hst,hinf]
  linarith only [hh]

theorem uniform_closed_population_bounded_of_increment {ι α : Type*}
    {V : ι → α → ℝ → Vec} {K : ι → Set α} {Q : ι → ℝ → ℝ}
    {T : ι → ℝ} {H M A P₀ Q₀ : ℝ}
    (hpos : ∀ i, 0 < T i) (hT : ∀ i, T i ≤ H) (hQ₀ : ∀ i, Q i 0 ≤ Q₀)
    (hQ : ∀ i, ContinuousOn (Q i) (Ico 0 (T i)))
    (hV : ∀ i z, z ∈ K i → ContinuousOn (V i z) (Icc 0 (T i)))
    (hmax : ∀ i t, t ∈ Ico 0 (T i) → ∀ z ∈ K i, q (V i z t) ≤ Q i t)
    (hattain : ∀ i t, t ∈ Ico 0 (T i) → ∃ z ∈ K i, Q i t = q (V i z t))
    (hM : 0 < M) (hA : 0 < A)
    (hincrement : ∀ i, PopulationIncrement (V i) (K i) (T i) M A P₀) :
    ∃ C : ℝ, ∀ i t, t ∈ Icc 0 (T i) → ∀ z ∈ K i, q (V i z t) ≤ C := by
  obtain ⟨C,hC⟩ := uniform_population_bounded_of_increment hT hQ₀ hQ
    (fun i z hz => (hV i z hz).mono Ico_subset_Icc_self) hmax hattain hM hA hincrement
  refine ⟨C,?_⟩
  intro i t ht z hz
  have he : closure (Ico (0:ℝ) (T i)) = Icc 0 (T i) := closure_Ico (ne_of_lt (hpos i))
  apply le_on_closure (fun t ht => hC i t ht z hz)
  · rw [he]
    exact ((contDiff_q (k:=1)).continuous.comp_continuousOn (hV i z hz))
  · exact continuousOn_const
  · rwa [he]

theorem compact_nonempty_uniform_population_bounded_of_increment
    {ι α : Type*} [TopologicalSpace α]
    {V : ι → α → ℝ → Vec} {K : ι → Set α} {T : ι → ℝ}
    {H M A P₀ Q₀ : ℝ}
    (hK : ∀ i, IsCompact (K i)) (hne : ∀ i, (K i).Nonempty)
    (hV : ∀ i, Continuous (fun p : ℝ × α => V i p.2 p.1))
    (hpos : ∀ i, 0 < T i) (hT : ∀ i, T i ≤ H)
    (hinit : ∀ i z, z ∈ K i → q (V i z 0) ≤ Q₀)
    (hM : 0 < M) (hA : 0 < A)
    (hincrement : ∀ i, PopulationIncrement (V i) (K i) (T i) M A P₀) :
    ∃ C : ℝ, ∀ i t, t ∈ Icc 0 (T i) → ∀ z ∈ K i, q (V i z t) ≤ C := by
  let Q : ι → ℝ → ℝ := fun i t => sSup ((fun z => q (V i z t)) '' K i)
  have hc (i : ι) : Continuous (fun p : ℝ × α => q (V i p.2 p.1)) :=
    (contDiff_q (k:=1)).continuous.comp (hV i)
  have hlabel (i : ι) (t : ℝ) : Continuous (fun z => q (V i z t)) := by
    have ht : Continuous (fun z : α => V i z t) :=
      (hV i).comp (Continuous.prodMk_right t)
    exact (contDiff_q (k:=1)).continuous.comp ht
  apply uniform_closed_population_bounded_of_increment (Q:=Q) hpos hT
  · intro i
    exact csSup_le ((hne i).image _) (fun y hy => by
      obtain ⟨z,hz,he⟩ := hy
      rw [←he]
      exact hinit i z hz)
  · intro i
    exact ((hK i).continuous_sSup (f:=fun t z => q (V i z t)) (hc i)).continuousOn
  · intro i z hz
    exact ((hV i).comp (Continuous.prodMk_left z)).continuousOn
  · intro i t ht z hz
    exact le_csSup ((hK i).image (hlabel i t)).bddAbove ⟨z,hz,rfl⟩
  · intro i t ht
    exact (hK i).exists_sSup_image_eq (hne i) (hlabel i t).continuousOn
  · exact hM
  · exact hA
  · exact hincrement

theorem compact_uniform_population_bounded_of_increment
    {ι α : Type*} [TopologicalSpace α]
    {V : ι → α → ℝ → Vec} {K : ι → Set α} {T : ι → ℝ}
    {H M A P₀ Q₀ : ℝ}
    (hK : ∀ i, IsCompact (K i))
    (hV : ∀ i, Continuous (fun p : ℝ × α => V i p.2 p.1))
    (hpos : ∀ i, 0 < T i) (hT : ∀ i, T i ≤ H)
    (hinit : ∀ i z, z ∈ K i → q (V i z 0) ≤ Q₀)
    (hM : 0 < M) (hA : 0 < A)
    (hincrement : ∀ i, PopulationIncrement (V i) (K i) (T i) M A P₀) :
    ∃ C : ℝ, ∀ i t, t ∈ Icc 0 (T i) → ∀ z ∈ K i, q (V i z t) ≤ C := by
  let J := {i : ι // (K i).Nonempty}
  obtain ⟨C,hC⟩ := compact_nonempty_uniform_population_bounded_of_increment
    (ι:=J) (V:=fun i=>V i.val) (K:=fun i=>K i.val)
    (fun i => hK i.val) (fun i => i.property) (fun i => hV i.val)
    (fun i => hpos i.val) (fun i => hT i.val) (fun i => hinit i.val)
    hM hA (fun i => hincrement i.val)
  refine ⟨C,?_⟩
  intro i t ht z hz
  exact hC ⟨i,⟨z,hz⟩⟩ t ht z hz

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PopulationIncrement.congr_on_prefix {α : Type*}
    {V W : α → ℝ → Vec} {K : Set α} {T M A P₀ : ℝ}
    (h : PopulationIncrement V K T M A P₀)
    (heq : ∀ z ∈ K, ∀ t ∈ Icc 0 T, V z t = W z t) :
    PopulationIncrement W K T M A P₀ := by
  intro τ hτ k hk hp z hz n a b ha hab hb hband
  have hsub : Icc (0:ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτ.2.le
  have hpre : ∀ t ∈ Icc 0 τ, ∀ y ∈ K, 1024*q (V y t) ≤ (2:ℝ)^k := by
    intro t ht y hy
    rw [heq y hy t (hsub ht)]
    exact hp t ht y hy
  have hh := h τ hτ k hk hpre z hz n a b ha hab hb
    (fun t ht => by
      rw [heq z hz t ⟨ha.trans ht.1,ht.2.trans (hb.trans hτ.2.le)⟩]
      exact hband t ht)
  rwa [heq z hz b ⟨ha.trans hab,hb.trans hτ.2.le⟩,
    heq z hz a ⟨ha,hab.trans (hb.trans hτ.2.le)⟩] at hh

theorem Admissible.uniform_physical_support_of_increment
    {ι : Type*} {d : Datum} (hd : Admissible d)
    {s : ι → Solution} {T : ι → ℝ} {H M A P₀ : ℝ}
    (hpos : ∀ i, 0 < T i) (hT : ∀ i, T i ≤ H)
    (F : ∀ i, PhaseFlowOn (s i).E (s i).B (T i))
    (hs : ∀ i, EnergyPrefix (s i) (T i))
    (h0 : ∀ i z, (s i).f (0,z) = d.f₀ z)
    (hM : 0 < M) (hA : 0 < A)
    (hincrement : ∀ i, PopulationIncrement (fun z t => ((F i).flow z t).2)
      (tsupport d.f₀) (T i) M A P₀) :
    ∃ P : ℝ, ∀ i t, t ∈ Icc 0 (T i) → ∀ x v, P < ‖v‖ → (s i).f (t,x,v) = 0 := by
  have hK : IsCompact (tsupport d.f₀) := hd.2.1
  have hcq : Continuous (fun z : Phase => q z.2) :=
    (contDiff_q (k:=1)).continuous.comp continuous_snd
  obtain ⟨Q₀,hQ₀⟩ := (hK.image hcq).bddAbove
  let V : ι → Phase → ℝ → Vec := fun i z t => (prefixFlow (F i).flow (T i) z t).2
  have heq (i : ι) (z : Phase) (t : ℝ) (ht : t ∈ Icc 0 (T i)) :
      ((F i).flow z t).2 = V i z t := by
    simp only [V,prefixFlow,prefixClamp_eq ht]
  have hinc (i : ι) : PopulationIncrement (V i) (tsupport d.f₀) (T i) M A P₀ :=
    (hincrement i).congr_on_prefix (fun z hz t ht => heq i z t ht)
  obtain ⟨P,hP⟩ := compact_uniform_population_bounded_of_increment
    (K:=fun _ : ι => tsupport d.f₀) (V:=V) (Q₀:=Q₀)
    (fun _ => hK) (fun i => ((F i).continuous_prefixFlow (hs i) (hpos i).le).snd)
    hpos hT
    (fun i z hz => by
      rw [←heq i z 0 ⟨le_rfl,(hpos i).le⟩,(F i).initial]
      exact hQ₀ ⟨z,hz,rfl⟩)
    hM hA hinc
  refine ⟨P,?_⟩
  intro i t ht x v hv
  by_contra hn
  have hflow : ∀ z, (s i).f (0,z) ≠ 0 → ∀ r ∈ Icc 0 (T i), q ((F i).flow z r).2 ≤ P := by
    intro z hz r hr
    have hz' : z ∈ tsupport d.f₀ := subset_tsupport _ (by change d.f₀ z ≠ 0; rwa [←h0 i z])
    rw [heq i z r hr]
    exact hP i r hr z hz'
  have hb := (F i).eulerian_supported_momentum (hs i) hflow ht x v hn
  exact (not_lt_of_ge hb) (hv.trans (norm_lt_q v))

end RVM

end

end OAI
