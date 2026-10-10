import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.DirectionOverlap
import OAI.Analysis.VlasovMaxwell.Population.DirectionCounts

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma pureOccupation_crude_scalar {I h H p : ℝ}
    (hI : 0≤I) (hh : 0≤h) (hH : 1≤H) (hp : 0<p) :
    (I+2*H*h)/(p/128)≤(1000000000*H^2)*(max I h/p) := by
  have hR : 0≤ max I h := hI.trans (le_max_left _ _)
  have hIH : I≤H*max I h := (le_max_left _ _).trans (le_mul_of_one_le_left hR hH)
  have hhH : H*h≤H*max I h := mul_le_mul le_rfl (le_max_right _ _) hh (by linarith)
  have hH2 : H≤H^2 := by nlinarith
  have hH0 : 0≤H := by linarith
  calc
    _=128*(I+2*H*h)/p := by ring
    _≤384*H*max I h/p := by
      apply div_le_div_of_nonneg_right _ hp.le
      nlinarith
    _≤(1000000000*H^2)*max I h/p := by gcongr; nlinarith
    _=_ := by ring

lemma pureOccupation_clipped_ratio {I lam h : ℝ} (hI : 0<I) (hlam : 0<lam) :
    1+I/min I (lam/2)≤4*max 1 (max (I/lam) (h/lam)) := by
  let R := max 1 (max (I/lam) (h/lam))
  have hR : 1≤R := le_max_left _ _
  have hIR : I/lam≤R := (le_max_left _ _).trans (le_max_right _ _)
  rcases le_total I (lam/2) with hc|hc
  · rw [min_eq_left hc,div_self hI.ne']; change _≤4*R; linarith
  · rw [min_eq_right hc]
    have he : I/(lam/2)=2*(I/lam) := by field_simp [hlam.ne']
    rw [he]; change _≤4*R; linarith

lemma pureOccupation_stable_scalar {I h H p lam : ℝ}
    (hI : 0<I) (hh : 0≤h) (hH : 1≤H) (hp : 0<p) (hlam : 0<lam) :
    35512320*(2*H*h)/p*(1+I/min I (lam/2))≤
      (1000000000*H^2)*((h/p)*max 1 (max (I/lam) (h/lam))) := by
  have hR : 0≤ max 1 (max (I/lam) (h/lam)) := zero_le_one.trans (le_max_left _ _)
  have hH0 : 0≤H := by linarith
  calc
    _≤35512320*(2*H*h)/p*(4*max 1 (max (I/lam) (h/lam))) :=
      mul_le_mul_of_nonneg_left (pureOccupation_clipped_ratio hI hlam) (by positivity)
    _=(284098560*H)*((h/p)*max 1 (max (I/lam) (h/lam))) := by ring
    _≤_ := by apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith

lemma pureOccupation_improved_scalar {I h H p I₀ φ : ℝ}
    (hh : 0≤h) (hH : 1≤H) (hp : 0<p) (hI₀ : 0<I₀) (hφ : 0≤φ) :
    2*(2*H*h)/(p/128)*φ^(-29/25:ℝ)*max 1 (max (I/I₀) ((2*H*h)/I₀))≤
      (1000000000*H^2)*((h/p)*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (h/I₀))) := by
  let R := max 1 (max (I/I₀) (h/I₀))
  have hR : 1≤R := le_max_left _ _
  have hHH : 1≤2*H := by linarith
  have hH0 : 0≤H := by linarith
  have hR' : max 1 (max (I/I₀) ((2*H*h)/I₀))≤2*H*R := by
    have hIR : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    have hhR : h/I₀≤R := (le_max_right _ _).trans (le_max_right _ _)
    have hR0 : R≤2*H*R := le_mul_of_one_le_left (zero_le_one.trans hR) hHH
    refine max_le (hR.trans hR0) (max_le (hIR.trans hR0) ?_)
    apply (div_le_iff₀ hI₀).mpr
    have hh' := mul_le_mul_of_nonneg_left ((div_le_iff₀ hI₀).mp hhR)
      (by positivity : 0≤2*H)
    simpa only [mul_assoc] using hh'
  calc
    _≤2*(2*H*h)/(p/128)*φ^(-29/25:ℝ)*(2*H*R) :=
      mul_le_mul_of_nonneg_left hR' (by positivity)
    _=(1024*H^2)*((h/p)*φ^(-29/25:ℝ)*R) := by ring
    _≤_ := by apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith

lemma ImprovedWindow.min_mass {P p w φ : ℝ} (h : ImprovedWindow P p w φ) :
    P^(7/10:ℝ)≤ min p w ∧ (min p w)^(-49/100:ℝ)≤φ ∧ φ≤(min p w)^(-4/25:ℝ) := by
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    exact ⟨h.1,h.2.2.1,by convert h.2.2.2.1 using 1; norm_num⟩
  · rw [min_eq_right hwp]
    exact ⟨h.2.1,h.2.2.2.2.1,by convert h.2.2.2.2.2 using 1; norm_num⟩

lemma pureOccupation_of_three {P C₀ C₁ M A p w φ h I K : ℝ} {O E : ℝ≥0∞}
    (hK : 0≤K)
    (h₀ : O≤ENNReal.ofReal (K*(max I h/p))*E)
    (h₁ : C₀/min p w<φ → O≤ENNReal.ofReal (K*((h/p)*max 1
      (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))))*E)
    (h₂ : ImprovedWindow P p w φ → O≤ENNReal.ofReal (K*((h/p)*φ^(-29/25:ℝ)*
      max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))))*E) :
    O≤ENNReal.ofReal (K*pureOccupationEnvelope P C₀ C₁ M A p w φ h I)*E := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs with ha hi hi <;>
    simp only [mul_min_of_nonneg _ _ hK,ENNReal.ofReal_min,min_mul]
  · exact le_min (le_min h₀ (h₁ ha)) (le_min h₀ (h₂ hi))
  · exact le_min (le_min h₀ (h₁ ha)) h₀
  · exact le_min h₀ (le_min h₀ (h₂ hi))
  · exact le_min h₀ h₀

namespace WeightedDirectionPartition
variable {V K : ℝ→Vec} {a b w δ : ℝ}

lemma halfopen_disjoint (D : WeightedDirectionPartition V K a b w δ)
    (i j : Fin D.count) (hne : i≠j) :
    Disjoint (Ico (D.time i) (D.time (i+1))) (Ico (D.time j) (D.time (j+1))) := by
  apply Ico_disjoint_Ico.mpr
  have hn : (i:ℕ)≠j := fun h=>hne (Fin.ext h)
  rcases lt_or_gt_of_ne hn with hij|hji
  · exact (min_le_left _ _).trans ((D.strict.monotoneOn (a := (i:ℕ)+1) (b := (j:ℕ)) (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_right _ _))
  · exact (min_le_right _ _).trans ((D.strict.monotoneOn (a := (j:ℕ)+1) (b := (i:ℕ)) (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_left _ _))

lemma halfopen_cover (D : WeightedDirectionPartition V K a b w δ) {t : ℝ}
    (ht : t∈Ico a b) : ∃i : Fin D.count,t∈Ico (D.time i) (D.time (i+1)) := by
  have ht' : t∈Ico (D.time 0) (D.time D.count) := by rwa [D.initial,D.terminal]
  obtain ⟨i,hi,hit⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico D.count D.time ht')
  exact ⟨⟨i,Finset.mem_range.mp hi⟩,hit⟩

lemma cell_direction_oscillation (D : WeightedDirectionPartition V K a b w δ)
    (i : Fin D.count) {s t : ℝ}
    (hs : s∈Icc (D.time i) (D.time (i+1))) (ht : t∈Icc (D.time i) (D.time (i+1))) :
    ‖momentumDirection (V t)-momentumDirection (V s)‖≤2*δ := by
  calc
    _≤‖momentumDirection (V t)-momentumDirection (V (D.time i))‖+
        ‖momentumDirection (V (D.time i))-momentumDirection (V s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤δ+δ := add_le_add (D.direction_control i i.isLt t ht)
      (by rw [norm_sub_rev]; exact D.direction_control i i.isLt s hs)
    _=_ := by ring

end WeightedDirectionPartition

lemma Admissible.exists_bounded_direction_partition {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b δ : ℝ) (k : ℕ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → b-a≤((2:ℝ)^k/P)^2 →
      P^(3/5:ℝ)≤(2:ℝ)^k → (2:ℝ)^k≤P → ((2:ℝ)^k)^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc ((2:ℝ)^k/8) (8*(2:ℝ)^k)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ∃ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b ((2:ℝ)^k) δ,
        (D.count:ℝ)≤C*(Real.log (2+P))^6/δ := by
  obtain ⟨C,hC,hcount⟩ := hd.direction_count_bound T₀ M A hM hA.le
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_direction_absorption 0] with P hcount hP
  intro s T F hs hT hTT zX a b δ k hz ha hb hab hlen hw hwP hδ hδ1 hsource hq HZ
  have hm := hP.2.2 ((2:ℝ)^k) δ hw hδ
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hV := (F.continuousOn_time zX).snd.mono hJ
  have hK : ContinuousOn (fun t=>s.E (t,(F.flow zX t).1)+
      cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) (Icc a b) := by
    apply ((F.continuous_prefixMomentumForce hs.energyPrefix hT zX).continuousOn).congr
    intro t ht
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJ ht),lorentzField,lorentzPhase]
  have hder (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun t=>(F.flow zX t).2)
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) t := by
    have hti : t∈Ioo (0:ℝ) T := ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
    exact ((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).snd
  obtain ⟨D⟩ := (HZ zX hz).weighted_direction_partition k hm.2.1 hab hJ hV hK hder hq
    hM hA (zero_lt_one.trans_le hP.1) (zero_lt_one.trans_le hP.2.1)
    ((Real.rpow_pos_of_pos (by positivity) (-3/5)).trans_le hδ)
  refine ⟨D,?_⟩
  exact hcount s T F hs hT hTT zX (tsupport d.f₀) a b ((2:ℝ)^k) δ hz hd.2.1 subset_rfl ha hb hab hlen hw hwP hδ hδ1
    hsource hq (fun t ht=>norm_momentum_of_high_band hm.2.1 (hq t ht).1) (HZ zX hz) HZ D

lemma PhaseFlowOn.momentum_le_on_initial_tsupport {d : Datum} {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (hP : ∀ z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    {z : Phase} (hz : z∈tsupport d.f₀) {r : ℝ} (hr : r∈Icc 0 T) :
    q (F.flow z r).2≤P := by
  have hc : Continuous (fun z=>q (prefixFlow F.flow T z r).2) :=
    (contDiff_q (k:=1)).continuous.comp
      (((F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_const.prodMk continuous_id)).snd)
  have hsub : Function.support d.f₀⊆{z | q (prefixFlow F.flow T z r).2≤P} := by
    intro z hz
    simpa only [mem_ofPred_eq,prefixFlow,prefixClamp_eq hr] using hP z (by simpa only [hs.initial_f,Function.mem_support] using hz) r hr
  have hh := closure_minimal hsub (isClosed_le hc continuous_const) hz
  simpa only [mem_ofPred_eq,prefixFlow,prefixClamp_eq hr] using hh

lemma momentum_ne_zero_of_band {v : Vec} {w : ℝ} (hw : 16≤w) (hq : w/8≤q v) : v≠0 := by
  intro he
  have hh := norm_momentum_of_high_band hw hq
  rw [he,norm_zero] at hh
  linarith

lemma inv_q_sq_le_of_lower {v : Vec} {m : ℝ} (hm : 0 < m) (h : m ≤ q v) :
    (q v)⁻¹ ^ 2 ≤ m⁻¹ ^ 2 := by
  gcongr
  exact inv_nonneg.mpr (q_pos v).le

lemma PhaseFlowOn.direction_partition_closed_duration {s : Solution} {T c d e w p δ ε φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    (DY : WeightedDirectionPartition (fun t=>(F.flow zY t).2)
      (fun t=>s.E (t,(F.flow zY t).1)+cross (velocity (F.flow zY t).2) (s.B (t,(F.flow zY t).1))) c d p δ)
    (DX : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
      (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) c e w δ)
    (hc : 0≤c) (hdT : d≤T) (heT : e≤T) (hde : d≤e)
    (hsnz : ∀t∈Icc c d,(F.flow zY t).2≠0)
    (hrnz : ∀t∈Icc c e,(F.flow zX t).2≠0)
    (hsq : ∀t∈Icc c d,(q (F.flow zY t).2)⁻¹^2≤ε)
    (hrq : ∀t∈Icc c e,(q (F.flow zX t).2)⁻¹^2≤ε)
    {H : Set ℝ} (hH : H⊆Icc c d)
    (hbin : ∀r∈H,∃t,InClosedConeBin F.flow zX B t r zY)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hφ : 0<φ)
    (hd : B.dmax≤φ^2/32) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hw : 4≤φ*B.wmin) (hsmall : 2*δ+2*ε≤φ/16) :
    volume H≤ENNReal.ofReal (((DY.count:ℝ)+DX.count)*(81*B.rmax)) := by
  classical
  choose arrival harr using hbin
  let ar : ℝ→ℝ := fun r=>if h:r∈H then arrival r h else 0
  have hsubY (i : Fin DY.count) : Ico (DY.time i) (DY.time (i+1))⊆Icc c d :=
    Ico_subset_Icc_self.trans (DY.cell_subset i.isLt)
  have hsubX (i : Fin DX.count) : Ico (DX.time i) (DX.time (i+1))⊆Icc c e :=
    Ico_subset_Icc_self.trans (DX.cell_subset i.isLt)
  have hb := F.direction_total_hit_duration zX zY B
    (fun i : Fin DY.count=>DY.time i) (fun i=>DY.time (i+1))
    (fun i : Fin DX.count=>DX.time i) (fun i=>DX.time (i+1))
    DY.halfopen_disjoint DX.halfopen_disjoint
    (fun i=>(hsubY i).trans (Icc_subset_Icc hc hdT))
    (fun i=>(hsubX i).trans (Icc_subset_Icc hc heT))
    (fun i t ht=>hsnz t (hsubY i ht)) (fun i t ht=>hrnz t (hsubX i ht))
    (fun i t ht=>hsq t (hsubY i ht)) (fun i t ht=>hrq t (hsubX i ht))
    (fun i a ha b hb=>DY.cell_direction_oscillation i (Ico_subset_Icc_self hb) (Ico_subset_Icc_self ha))
    (fun i a ha b hb=>DX.cell_direction_oscillation i (Ico_subset_Icc_self hb) (Ico_subset_Icc_self ha))
    (H:=H\{d}) ar
    (fun r hr=>DY.halfopen_cover ⟨(hH hr.1).1,lt_of_le_of_ne (hH hr.1).2 (by simpa using hr.2)⟩)
    (fun r hr=>DX.halfopen_cover ⟨(hH hr.1).1,(lt_of_le_of_ne (hH hr.1).2 (by simpa using hr.2)).trans_le hde⟩)
    (fun r hr=>by simpa only [ar,dite_eq_left hr.1] using harr r hr.1)
    hr hrmax hφ hd hDlo hDhi hw hsmall
  rw [measure_sdiff_null (measure_singleton d)] at hb
  simpa only [Fintype.card_fin,ENNReal.ofReal_mul (by positivity : 0≤(DY.count:ℝ)+DX.count),
    ENNReal.ofReal_add (by positivity : 0≤(DY.count:ℝ)) (by positivity : 0≤(DX.count:ℝ)),
    ENNReal.ofReal_natCast] using hb

lemma Admissible.exists_stable_direction_partition {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (z : Phase) (a b r m δ : ℝ),
      z∈tsupport d.f₀ → 0≤a → b≤T → r∈Icc a b → 0 < m → m≤q (F.flow z r).2 →
      b-a≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      b-a≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ∃ k : ℕ, ∃ D : WeightedDirectionPartition (fun t=>(F.flow z t).2)
        (fun t=>s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) a b ((2:ℝ)^k) δ,
        (D.count:ℝ)≤C*(Real.log (2+P))^6/δ ∧ 16≤(2:ℝ)^k ∧
        (∀t∈Icc a b,m/2≤q (F.flow z t).2 ∧ (F.flow z t).2≠0) := by
  obtain ⟨C,hC,hcount⟩ := hd.exists_bounded_direction_partition T₀ M A hM hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_direction_absorption 0] with P hcount hlarge
  intro s T F hs hT hTT z a b r m δ hz ha hb hr hm hmq hlen hlen' hhigh hδ hδ1 hsource HZ
  have hp : 0<P := zero_lt_one.trans_le hlarge.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hlarge.2.1
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hstable := (HZ z hz).velocity_stability_scale ha hb hr
    ((F.continuousOn_time z).snd.mono hJ) hM hA.le hp hL hm
    (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (128:ℝ)≤128) hmq
    (by simpa only [div_one] using hlen)
  obtain ⟨k,hkq,hqk⟩ := exists_nat_pow_near (one_le_q (F.flow z r).2) (by norm_num : (1:ℝ)<2)
  have href : q (F.flow z r).2≤2*(2:ℝ)^k := by rw [pow_succ] at hqk; nlinarith
  have hmk : m/2≤(2:ℝ)^k := by linarith
  have hkP : (2:ℝ)^k≤P := hkq.trans (F.momentum_le_on_initial_tsupport hs hT hsource hz (hJ hr))
  have hkδ : ((2:ℝ)^k)^(-3/5:ℝ)≤δ :=
    (Real.rpow_le_rpow_of_nonpos (half_pos hm) hmk (by norm_num)).trans hδ
  have hband : ∀t∈Icc a b,q (F.flow z t).2∈Icc ((2:ℝ)^k/8) (8*(2:ℝ)^k) := by
    intro t ht
    have hh := (hstable t ht).2.2
    constructor <;> nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) k]
  have hm16 := (hlarge.2.2 ((2:ℝ)^k) δ (hhigh.trans hmk) hkδ).2.1
  obtain ⟨D,hD⟩ := hcount s T F hs hT hTT z a b δ k hz ha hb (hr.1.trans hr.2)
    (hlen'.trans (by gcongr)) (hhigh.trans hmk) hkP hkδ hδ1 hsource hband HZ
  refine ⟨k,D,hD,hm16,?_⟩
  intro t ht
  exact ⟨by linarith [(hstable t ht).2.2.1],momentum_ne_zero_of_band hm16 (hband t ht).1⟩

lemma Admissible.direction_stable_closed_cell_bound {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b c d e m δ φ : ℝ),
      zX∈tsupport d₀.f₀ → 0≤c → c≤d → d≤e → e≤T → Icc a b⊆Icc c e →
      0 < m → m≤B.qmin → m≤B.wmin →
      e-c≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      e-c≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      0<B.rmin → 0≤B.rmax → 0<φ →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
      2*δ+2*((m/2)⁻¹)^2≤φ/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ENNReal.ofReal (B.qmin/2)*labelOccupation (fun z=>s.f (0,z))
        (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d)≤
      ENNReal.ofReal (C*B.rmax*(Real.log (2+P))^6/δ)*ENNReal.ofReal (datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hpart⟩ := hd₀.exists_stable_direction_partition T₀ M A hM hA
  refine ⟨162*C,by positivity,?_⟩
  filter_upwards [hpart,eventually_direction_absorption 0] with P hpart hlarge
  intro s T F hs hT hTT zX B a b c d e m δ φ hzX hc hcd hde he hJ hm hmq hmw hstable hlen hhigh hδ hδ1
    hr hrmax hφ hd hDlo hDhi hw hsmall hsource HZ
  have hp : 0<P := zero_lt_one.trans_le hlarge.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hlarge.2.1
  have hδ0 : 0<δ := (Real.rpow_pos_of_pos (half_pos hm) (-3/5)).trans_le hδ
  have hCtime : Icc c d⊆Icc 0 T := Icc_subset_Icc hc (hde.trans he)
  have hdata : ∀ z,(closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z)≤
          ENNReal.ofReal (162*C*B.rmax*(Real.log (2+P))^6/δ) ∧
        B.qmin/2≤q (F.flow z c).2 := by
    intro z hz
    obtain ⟨r,hzS,hrC,t,htJ,hbin⟩ := hz
    have hqm : m≤q (F.flow z r).2 := hmq.trans hbin.2.2.1.1
    have hwm : m≤q (F.flow zX t).2 := hmw.trans hbin.2.2.2.1.1
    obtain ⟨kY,DY,hDY,hkY,hqY⟩ := hpart s T F hs hT hTT z c d r m δ hzS hc (hde.trans he) hrC hm hqm
      ((by linarith : d-c≤e-c).trans hstable) ((by linarith : d-c≤e-c).trans hlen)
      hhigh hδ hδ1 hsource HZ
    obtain ⟨kX,DX,hDX,hkX,hqX⟩ := hpart s T F hs hT hTT zX c e t m δ hzX hc he (hJ htJ) hm hwm
      hstable hlen hhigh hδ hδ1 hsource HZ
    constructor
    · have hbound := F.direction_partition_closed_duration zX z B DY DX hc (hde.trans he) he hde
        (fun r hr=>(hqY r hr).2) (fun r hr=>(hqX r hr).2)
        (fun r hr=>inv_q_sq_le_of_lower (half_pos hm) (hqY r hr).1)
        (fun r hr=>inv_q_sq_le_of_lower (half_pos hm) (hqX r hr).1)
        (H:=closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z)
        (fun _ hh=>hh.2.1) (fun r hh=>by obtain ⟨_,_,t,_,ht⟩:=hh; exact ⟨t,ht⟩)
        hr hrmax hφ hd hDlo hDhi hw hsmall
      refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
      calc
        _≤(C*(Real.log (2+P))^6/δ+C*(Real.log (2+P))^6/δ)*(81*B.rmax) :=
          mul_le_mul_of_nonneg_right (add_le_add hDY hDX) (by positivity)
        _=_ := by ring
    · have hh := (HZ z hzS).velocity_stability_scale hc (hde.trans he) hrC
        ((F.continuousOn_time z).snd.mono hCtime) hM hA.le hp hL hm
        (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (128:ℝ)≤128) hqm
        (by simpa only [div_one] using ((by linarith : d-c≤e-c).trans hstable)) c (left_mem_Icc.mpr hcd)
      linarith [hh.2.2.1,hbin.2.2.1.1]
  rw [←hs.initial_energy_eq]
  apply F.label_occupation_cell_bound hs.energyPrefix (hCtime (left_mem_Icc.mpr hcd))
  · intro z
    by_cases hz : (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz=>(hdata z hz).2

lemma Admissible.direction_closed_bin_grid {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b m δ φ len : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<len →
      0 < m → m≤B.qmin → m≤B.wmin →
      2*len≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      2*len≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      0<B.rmin → 0≤B.rmax → B.rmax≤len → 0<φ →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
      2*δ+2*((m/2)⁻¹)^2≤φ/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ENNReal.ofReal (B.qmin/2)*labelOccupation (fun z=>s.f (0,z))
        (closedBinHits F.flow zX B (tsupport d₀.f₀) a b 0 T)≤
      ENNReal.ofReal (C*B.rmax*(Real.log (2+P))^6/δ)*
        ENNReal.ofReal ((2+(b-a+B.rmax)/len)*datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hcell⟩ := hd₀.direction_stable_closed_cell_bound T₀ M A hM hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hcell] with P hcell
  intro s T F hs hT hTT zX B a b m δ φ len hzX ha hb hab hlen hm hmq hmw hstable hlen' hhigh hδ hδ1
    hr hrmax hrad hφ hd hDlo hDhi hw hsmall hsource HZ
  classical
  let l := sourceCellLo len
  let u := sourceCellHi T len
  let e := fun i=>min T (u i+B.rmax)
  let N := selectedSourceCells T len a b B.rmax
  let D := C*B.rmax*(Real.log (2+P))^6/δ
  let O := fun i=>labelOccupation (fun z=>s.f (0,z))
    (closedBinHits F.flow zX B (tsupport d₀.f₀) a b (l i) (u i))
  have hgrid (i : ℕ) (hi : i∈N) :
      0≤l i ∧ l i≤u i ∧ u i≤T ∧ u i-l i≤len :=
    selectedSourceCells_subset_prefix hT hlen hi
  have hJC (i : ℕ) : Icc (max a (l i)) (min b (u i+B.rmax))⊆Icc (l i) (e i) := by
    intro t ht
    exact ⟨(le_max_right _ _).trans ht.1,
      le_min ((ht.2.trans (min_le_left _ _)).trans hb) (ht.2.trans (min_le_right _ _))⟩
  have hue (i : ℕ) (hi : i∈N) : u i≤e i :=
    le_min (hgrid i hi).2.2.1 (by linarith)
  have hST (i : ℕ) (hi : i∈N) : e i-l i≤2*len := by
    have hg := (hgrid i hi).2.2.2
    have hw' : e i≤u i+B.rmax := min_le_right _ _
    linarith
  have hsum : labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B (tsupport d₀.f₀) a b 0 T)≤∑i∈N,O i := by
    rw [closedBinHits_clip_source]
    apply F.closedBinHits_occupation_le_sum hs.energyPrefix hT zX B hd₀.2.1 N l u (Icc_subset_Icc ha hb)
    · intro i hi
      exact Icc_subset_Icc (hgrid i hi).1 (hgrid i hi).2.2.1
    · exact selectedSourceCells_cover hlen
  have hpay (i : ℕ) (hi : i∈N) : ENNReal.ofReal (B.qmin/2)*O i≤
      ENNReal.ofReal D*ENNReal.ofReal (datumEnergyNumber d₀) := by
    dsimp only [O]
    rw [closedBinHits_clip_receiver]
    exact hcell s T F hs hT hTT zX B (max a (l i)) (min b (u i+B.rmax)) (l i) (u i) (e i)
      m δ φ hzX (hgrid i hi).1 (hgrid i hi).2.1 (hue i hi) (min_le_left _ _) (hJC i)
      hm hmq hmw ((hST i hi).trans hstable) ((hST i hi).trans hlen') hhigh hδ hδ1
      hr hrmax hφ hd hDlo hDhi hw hsmall hsource HZ
  have hcount : (N.card:ℝ≥0∞)≤ENNReal.ofReal (2+(b-a+B.rmax)/len) := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (selectedSourceCells_card hlen hab hrmax)
  calc
    _ ≤ ENNReal.ofReal (B.qmin/2)*(∑i∈N,O i) := mul_le_mul' le_rfl hsum
    _ = ∑i∈N,ENNReal.ofReal (B.qmin/2)*O i := Finset.mul_sum _ _ _
    _ ≤ ∑i∈N,ENNReal.ofReal D*ENNReal.ofReal (datumEnergyNumber d₀) := Finset.sum_le_sum hpay
    _ = (N.card:ℝ≥0∞)*(ENNReal.ofReal D*ENNReal.ofReal (datumEnergyNumber d₀)) := by simp
    _ ≤ ENNReal.ofReal (2+(b-a+B.rmax)/len)*(ENNReal.ofReal D*ENNReal.ofReal (datumEnergyNumber d₀)) :=
      mul_le_mul' hcount le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0≤2+(b-a+B.rmax)/len)]
      dsimp only [D]
      ac_rfl

lemma Admissible.direction_closedEulerian_grid {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b m δ φ len : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<len →
      0 < m → m≤B.qmin → m≤B.wmin →
      2*len≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      2*len≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      0<B.rmin → 0≤B.rmax → B.rmax≤len → 0<φ →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
      2*δ+2*((m/2)⁻¹)^2≤φ/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (2*C*B.rmax/B.qmin*(Real.log (2+P))^6/δ*(2+(b-a+B.rmax)/len))*
        ENNReal.ofReal (datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hgrid⟩ := hd₀.direction_closed_bin_grid T₀ M A hM hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hgrid] with P hgrid
  intro s T F hs hT hTT zX B a b m δ φ len hzX ha hb hab hlen hm hmq hmw hstable hlen' hhigh hδ hδ1
    hr hrmax hrad hφ hd hDlo hDhi hw hsmall hsource HZ
  have hq0 : 0<B.qmin := hm.trans_le hmq
  have hδ0 : 0<δ := (Real.rpow_pos_of_pos (half_pos hm) (-3/5)).trans_le hδ
  have ho := hgrid s T F hs hT hTT zX B a b m δ φ len hzX ha hb hab hlen hm hmq hmw hstable hlen'
    hhigh hδ hδ1 hr hrmax hrad hφ hd hDlo hDhi hw hsmall hsource HZ
  have hbnd := mul_le_mul' (le_refl ((ENNReal.ofReal (B.qmin/2))⁻¹)) ho
  rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (half_pos hq0)).ne'
    ENNReal.ofReal_ne_top,one_mul] at hbnd
  have he := F.closedBinEulerian_occupation_le (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin))
    hs.energyPrefix hT zX B hd₀.2.1 (Icc_subset_Icc ha hb)
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  refine he.trans ((show labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B (tsupport d₀.f₀) a b 0 T) from ?_).trans ?_)
  · unfold labelOccupation
    apply lintegral_mono
    intro z
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro u ⟨hz,hu,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hu.1,hu.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩
  · apply hbnd.trans_eq
    rw [ENNReal.ofReal_mul (by positivity : 0≤2+(b-a+B.rmax)/len)]
    rw [←ENNReal.ofReal_inv_of_pos (half_pos hq0)]
    rw [←mul_assoc,←mul_assoc,←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp

lemma eventually_log_power_le_positive_rpow (k : ℕ) (ε D : ℝ) (hε : 0<ε) :
    ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
  have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
  filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
  have hp0 : 0<P := by linarith
  have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
  have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2+P)≤2*Real.log P := by
    calc
      _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
      _=_ := by rw [Real.log_pow]; norm_num
  have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
    simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
      one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
  calc
    D*(Real.log (2+P))^k≤|D| *(Real.log (2+P))^k :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _≤|D| *(2*Real.log P)^k := by
      have h : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
      gcongr
    _=|D*2^k| *(Real.log P)^k := by
      rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
    _≤_ := hbo

lemma eventually_direction_window :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ m φ : ℝ, P^(7/10:ℝ)≤ m → m^(-49/100:ℝ)≤φ → φ≤ m^(-4/25:ℝ) →
        0 < m ∧ 0<φ ∧ φ≤1 ∧ P^(3/5:ℝ)≤(m/128)/2 ∧
        ((m/128)/2)^(-3/5:ℝ)≤φ/128 ∧
        512≤ m*φ ∧ 2*(φ/128)+2*(((m/128)/2)⁻¹)^2≤φ/16 ∧
        φ≤P^(-14/125:ℝ) := by
  have hc : ∀ᶠ P : ℝ in atTop, 256≤P^(1/10:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop 256
  have hd : ∀ᶠ P : ℝ in atTop, 128*(256:ℝ)^(3/5:ℝ)≤P^(77/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<77/1000)).eventually_ge_atTop _
  have hg : ∀ᶠ P : ℝ in atTop, 512≤P^(357/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<357/1000)).eventually_ge_atTop _
  have he : ∀ᶠ P : ℝ in atTop, 4194304≤P^(1057/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1057/1000)).eventually_ge_atTop _
  filter_upwards [hc,hd,hg,he,eventually_direction_absorption 0] with P hc hd hg he hlarge
  refine ⟨hlarge.1,hlarge.2.1,?_⟩
  intro m φ hPm hlo hhi
  have hP := hlarge.1
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hm1 : 1≤ m := (Real.one_le_rpow hP (by norm_num : (0:ℝ)≤7/10)).trans hPm
  have hm : 0 < m := zero_lt_one.trans_le hm1
  have hφ : 0<φ := (Real.rpow_pos_of_pos hm _).trans_le hlo
  have hφ1 : φ≤1 := hhi.trans (Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num))
  have hexp (α : ℝ) (hα : 0≤α) : P^((7/10)*α)≤ m^α := by
    rw [Real.rpow_mul hP0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hP0.le _) hPm hα
  have hhigh : P^(3/5:ℝ)≤(m/128)/2 := by
    have hh := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hP0.le (3/5))
    rw [←Real.rpow_add hP0] at hh
    norm_num at hh
    linarith
  have hstep : ((m/128)/2)^(-3/5:ℝ)≤φ/128 := by
    have hh : 128*(256:ℝ)^(3/5:ℝ)≤ m^(11/100:ℝ) :=
      hd.trans (by have hh := hexp (11/100) (by norm_num); norm_num at hh; exact hh)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hm.le (-3/5))
    rw [←Real.rpow_add hm] at hh'
    norm_num at hh'
    have heq : ((m/128)/2)^(-3/5:ℝ)=m^(-3/5:ℝ)*(256:ℝ)^(3/5:ℝ) := by
      rw [show m/128/2=m/256 by ring,Real.div_rpow hm.le (by norm_num)]
      have hh : (256:ℝ)^(-3/5:ℝ)=((256:ℝ)^(3/5:ℝ))⁻¹ := by
        rw [show (-3/5:ℝ)=-(3/5) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤256)]
      rw [hh,div_inv_eq_mul]
    rw [heq]
    nlinarith
  have hgeom : 512≤ m*φ := by
    have hh : 512≤ m^(51/100:ℝ) := hg.trans (by have hh := hexp (51/100) (by norm_num); norm_num at hh; exact hh)
    have heq : m^(51/100:ℝ)=m*m^(-49/100:ℝ) := by
      calc
        _=m^((1:ℝ)+(-49/100)) := by norm_num
        _=m^(1:ℝ)*m^(-49/100:ℝ) := Real.rpow_add hm _ _
        _=_ := by rw [Real.rpow_one]
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlo hm.le)
  have hdef : (((m/128)/2)⁻¹)^2≤φ/64 := by
    have hh : 4194304≤ m^(151/100:ℝ) := he.trans (by have hh := hexp (151/100) (by norm_num); norm_num at hh; exact hh)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hm.le (-2))
    rw [←Real.rpow_add hm] at hh'
    norm_num at hh'
    have heq : (((m/128)/2)⁻¹)^2=65536*(m^2)⁻¹ := by field_simp; ring
    rw [heq]
    linarith
  have hupper : φ≤P^(-14/125:ℝ) := by
    apply hhi.trans
    calc
      m^(-4/25:ℝ)≤(P^(7/10:ℝ))^(-4/25:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hP0 _) hPm (by norm_num)
      _=_ := by rw [←Real.rpow_mul hP0.le]; norm_num
  exact ⟨hm,hφ,hφ1,hhigh,hstep,hgeom,by linarith,hupper⟩

lemma eventually_direction_window_absorption (D : ℝ) :
    ∀ᶠ P : ℝ in atTop, ∀ φ : ℝ,0<φ → φ≤P^(-14/125:ℝ) →
      D*(Real.log (2+P))^7≤φ^(-4/25:ℝ) := by
  filter_upwards [eventually_log_power_le_positive_rpow 7 (56/3125) D (by norm_num),
    eventually_gt_atTop (0:ℝ)] with P hlog hP
  intro φ hφ hφP
  calc
    _≤P^(56/3125:ℝ) := hlog
    _=(P^(-14/125:ℝ))^(-4/25:ℝ) := by rw [←Real.rpow_mul hP.le]; norm_num
    _≤φ^(-4/25:ℝ) := Real.rpow_le_rpow_of_nonpos hφ hφP (by norm_num)

def directionGridRate (M A L : ℝ) : ℝ :=
  131072+536870912*(M+Real.sqrt (A*L))^2

def directionGridConstant (M A : ℝ) : ℝ :=
  131072+1073741824*(M^2+A)

lemma directionGridRate_lower (M A L : ℝ) : 131072≤directionGridRate M A L := by
  unfold directionGridRate
  exact le_add_of_nonneg_right (by positivity)

lemma directionGridConstant_pos {M A : ℝ} (hA : 0≤A) : 0<directionGridConstant M A := by
  unfold directionGridConstant
  positivity

lemma directionGridRate_log_bound {M A L : ℝ} (hA : 0≤A) (hL : 1≤L) :
    directionGridRate M A L≤directionGridConstant M A*L := by
  have hAL : 0≤A*L := mul_nonneg hA (zero_le_one.trans hL)
  have hs := Real.sq_sqrt hAL
  have hc := sq_nonneg (M-Real.sqrt (A*L))
  have hML := mul_le_mul_of_nonneg_left hL (sq_nonneg M)
  unfold directionGridRate directionGridConstant
  nlinarith

lemma directionGridLength_scales {P M A L m : ℝ} (hP : 0<P) (hM : 0<M) (hm : 0 < m) :
    let len := (m/P)^2/directionGridRate M A L
    0<len ∧
    2*len≤(128*(P/(m/128))*(M+Real.sqrt (A*L)))⁻¹^2 ∧
    2*len≤((m/128)/2/P)^2 := by
  dsimp only
  let Q := directionGridRate M A L
  let S := M+Real.sqrt (A*L)
  have hQlower : 131072≤Q := directionGridRate_lower M A L
  have hQ : 0<Q := by linarith
  have hS : 0<S := add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
  have hI : 0<(m/P)^2 := sq_pos_of_pos (div_pos hm hP)
  have heq : (128*(P/(m/128))*(M+Real.sqrt (A*L)))⁻¹^2=
      (m/P)^2/(268435456*S^2) := by
    dsimp only [S]
    field_simp
    ring
  refine ⟨div_pos hI hQ,?_,?_⟩
  · rw [heq]
    change 2*((m/P)^2/Q)≤_
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hQ (by positivity : 0<268435456*S^2)).mpr
    have hh : 2*(268435456*S^2)≤Q := by dsimp [Q,directionGridRate,S]; nlinarith
    nlinarith
  · change 2*((m/P)^2/Q)≤_
    have heq' : ((m/128)/2/P)^2=(m/P)^2/65536 := by ring
    rw [heq',←mul_div_assoc]
    apply (div_le_div_iff₀ hQ (by norm_num : (0:ℝ)<65536)).mpr
    nlinarith

lemma direction_grid_count_scalar {I r I₀ Q : ℝ} (hI₀ : 0<I₀) (hQ : 1≤Q) :
    2+(I+r)/(I₀/Q)≤4*Q*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 1≤R := le_max_left _ _
  have hIQ : I≤I₀*R := by
    have hh : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hrQ : r≤I₀*R := by
    have hh : r/I₀≤R := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hQ0 : 0<Q := zero_lt_one.trans_le hQ
  have hdiv : (I+r)/(I₀/Q)≤2*Q*R := by
    apply (div_le_iff₀ (div_pos hI₀ hQ0)).mpr
    have he : 2*Q*R*(I₀/Q)=2*I₀*R := by field_simp
    rw [he]
    linarith
  have hQR : R≤Q*R := le_mul_of_one_le_left (zero_le_one.trans hR) hQ
  change _≤4*Q*R
  linarith

lemma direction_short_occupation_scalar {C Cq L Q I₀ I r q φ : ℝ}
    (hC : 0≤C) (_ : 0≤Cq) (hL : 1≤L) (hQ : 1≤Q) (hQL : Q≤Cq*L)
    (hI₀ : 0<I₀) (hr : 0≤r) (hq : 0<q) (hφ : 0<φ)
    (habs : 1024*C*Cq*L^7≤φ^(-4/25:ℝ)) :
    2*C*r/q*L^6/(φ/128)*(2+(I+r)/(I₀/Q))≤
      r/q*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 0≤R := zero_le_one.trans (le_max_left _ _)
  have hL0 := zero_le_one.trans hL
  have hcount := direction_grid_count_scalar (I:=I) (r:=r) hI₀ hQ
  have hpowers : φ^(-4/25:ℝ)/φ=φ^(-29/25:ℝ) := by
    calc
      _=φ^(-4/25:ℝ)/φ^(1:ℝ) := by rw [Real.rpow_one]
      _=φ^((-4/25)-1:ℝ) := (Real.rpow_sub hφ _ _).symm
      _=_ := by norm_num
  calc
    _≤2*C*r/q*L^6/(φ/128)*(4*Q*R) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _≤2*C*r/q*L^6/(φ/128)*(4*(Cq*L)*R) := by gcongr
    _=(1024*C*Cq*L^7)*(r/q/φ*R) := by ring
    _≤φ^(-4/25:ℝ)*(r/q/φ*R) := mul_le_mul_of_nonneg_right habs (by positivity)
    _=r/q*(φ^(-4/25:ℝ)/φ)*R := by ring
    _=_ := by rw [hpowers]

lemma direction_long_occupation_scalar {I₀ Q I r q φ : ℝ}
    (hI₀ : 0<I₀) (hQ : 1≤Q) (hr : I₀/Q≤r) (hq : 0<q)
    (habs : Q≤φ^(-29/25:ℝ)) :
    (I+r)/q≤2*r/q*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (r/I₀)) := by
  let R := max 1 (max (I/I₀) (r/I₀))
  have hR : 1≤R := le_max_left _ _
  have hQ0 := zero_lt_one.trans_le hQ
  have hr0 : 0<r := (div_pos hI₀ hQ0).trans_le hr
  have hI₀r : I₀≤r*Q := (div_le_iff₀ hQ0).mp hr
  have hIR : I≤I₀*R := by
    have hh : I/I₀≤R := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hI₀).mp hh |>.trans_eq (mul_comm _ _)
  have hIr : I≤r*Q*R := hIR.trans (mul_le_mul_of_nonneg_right hI₀r (zero_le_one.trans hR))
  have hrR : r≤r*Q*R := by
    exact (le_mul_of_one_le_right hr0.le hQ).trans (le_mul_of_one_le_right (by positivity) hR)
  calc
    (I+r)/q≤(2*r*Q*R)/q := div_le_div_of_nonneg_right (by linarith) hq.le
    _≤(2*r*φ^(-29/25:ℝ)*R)/q := by gcongr
    _=_ := by ring

lemma Admissible.direction_closedEulerian_improved {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b m φ I : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → b-a≤I →
      m/128≤B.qmin → m/128≤B.wmin →
      P^(7/10:ℝ)≤ m → m^(-49/100:ℝ)≤φ → φ≤ m^(-4/25:ℝ) →
      0<B.rmin → 0≤B.rmax →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (2*B.rmax/B.qmin*φ^(-29/25:ℝ)*
        max 1 (max (I/(m/P)^2) (B.rmax/(m/P)^2)))*ENNReal.ofReal (datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hgrid⟩ := hd₀.direction_closedEulerian_grid T₀ M A hM hA
  let Cq := directionGridConstant M A
  have hCq : 0<Cq := directionGridConstant_pos hA.le
  let D := Cq+1024*C*Cq
  filter_upwards [hgrid,eventually_direction_window,eventually_direction_window_absorption D]
    with P hgrid hwindow habs
  intro s T F hs hT hTT zX B a b m φ I hzX ha hb hab hJI hmq hmw hhigh hlo hhi hr hrmax hd hDlo hDhi hsource HZ
  have hP : 0<P := zero_lt_one.trans_le hwindow.1
  have hL := hwindow.2.1
  obtain ⟨hm,hφ,hφ1,hhigh',hstep,hgeom,hsmall,hφP⟩ := hwindow.2.2 m φ hhigh hlo hhi
  have hq : 0<B.qmin := (by positivity : 0< m/128).trans_le hmq
  have hw : 4≤φ*B.wmin := by
    have hh := mul_le_mul_of_nonneg_left hmw hφ.le
    nlinarith
  let L := Real.log (2+P)
  let Q := directionGridRate M A L
  let I₀ := (m/P)^2
  let len := I₀/Q
  have hI₀ : 0<I₀ := sq_pos_of_pos (div_pos hm hP)
  have hQlower : 131072≤Q := directionGridRate_lower M A L
  have hQ : 1≤Q := by linarith
  have hQL : Q≤Cq*L := directionGridRate_log_bound hA.le hL
  have hscales := directionGridLength_scales (A:=A) (L:=L) hP hM hm
  have hlen : 0<len := hscales.1
  have h7 : L≤L^7 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (show 1≤7 by norm_num))
  have hAbs : D*L^7≤φ^(-4/25:ℝ) := habs φ hφ hφP
  have hAbsShort : 1024*C*Cq*L^7≤φ^(-4/25:ℝ) := by
    apply le_trans _ hAbs
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [D]
    linarith
  have hpowers : φ^(-4/25:ℝ)/φ=φ^(-29/25:ℝ) := by
    calc
      _=φ^(-4/25:ℝ)/φ^(1:ℝ) := by rw [Real.rpow_one]
      _=φ^((-4/25)-1:ℝ) := (Real.rpow_sub hφ _ _).symm
      _=_ := by norm_num
  have hQabs : Q≤φ^(-29/25:ℝ) := by
    calc
      Q≤Cq*L := hQL
      _≤Cq*L^7 := mul_le_mul_of_nonneg_left h7 hCq.le
      _≤D*L^7 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [D]
        nlinarith
      _≤φ^(-4/25:ℝ) := hAbs
      _≤φ^(-4/25:ℝ)/φ := by
        apply (le_div_iff₀ hφ).mpr
        exact mul_le_of_le_one_right (Real.rpow_nonneg hφ.le _) hφ1
      _=_ := hpowers
  by_cases hrad : B.rmax≤len
  · have ho := hgrid s T F hs hT hTT zX B a b (m/128) (φ/128) φ len
      hzX ha hb hab hlen (by positivity) hmq hmw hscales.2.1 hscales.2.2 hhigh' hstep
      (by linarith) hr hrmax hrad hφ hd hDlo hDhi hw hsmall hsource HZ
    have hscalar := direction_short_occupation_scalar hC.le hCq.le hL hQ hQL hI₀ hrmax hq hφ hAbsShort
      (I:=I)
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    calc
      _≤2*C*B.rmax/B.qmin*L^6/(φ/128)*(2+(I+B.rmax)/len) := by
        have hL0 : 0≤L := zero_le_one.trans hL
        gcongr
      _≤B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀)) := hscalar
      _≤_ := by
        have hR : 0≤ max 1 (max (I/I₀) (B.rmax/I₀)) := zero_le_one.trans (le_max_left _ _)
        have hn : 0≤B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀)) := by positivity
        calc
          _≤2*(B.rmax/B.qmin*φ^(-29/25:ℝ)*max 1 (max (I/I₀) (B.rmax/I₀))) :=
            le_mul_of_one_le_left hn (by norm_num)
          _=_ := by dsimp only [I₀]; ring

  · have ho := F.closedEulerian_crude_budget hs.energyPrefix hT zX B hd₀.2.1 (Icc_subset_Icc ha hb) hJI hr.le hq
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq]
    exact ENNReal.ofReal_le_ofReal (direction_long_occupation_scalar hI₀ hQ (le_of_not_ge hrad) hq hQabs)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.representative_pure_occupation {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal ((1000000000*(max 1 T₀)^2)*pureOccupationEnvelope P 512 16384 M A
        (sourceRepresentative (k 0)) w (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I)*
        ENNReal.ofReal (datumEnergyNumber d₀) := by
  filter_upwards [hd₀.direction_closedEulerian_improved T₀ M A hM hA,eventually_direction_window]
    with P himproved hwindow
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let H₀ := max 1 T₀
  let B := representativeClosedBin T w k
  let E := ENNReal.ofReal (datumEnergyNumber d₀)
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH₀ : 1≤H₀ := le_max_left _ _
  have hHH : H≤H₀ := max_le_max le_rfl hTT
  have hP : 0<P := zero_lt_one.trans_le hwindow.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hwindow.2.1
  have hKH : 1000000000*H^2≤1000000000*H₀^2 := by gcongr
  have hq : 0<B.qmin := by change 0<p/128; positivity
  have hr : 0<B.rmin := representativeClosedBin_radius_pos T w k
  have hrmax : 0≤B.rmax := by change 0≤2*H*h; positivity
  have hd : B.dmax≤φ^2/32 := by
    have hθ := (cappedRepresentative_pos (k 1)).le
    have hh' := sq_le_sq₀ hθ (by positivity : 0≤φ/16) |>.mpr hsmall
    change 8*(cappedRepresentative (k 1))^2≤φ^2/32
    nlinarith
  have hcrude : O≤ENNReal.ofReal ((1000000000*H₀^2)*(max I h/p))*E := by
    have ho := F.closedEulerian_crude_budget hs.energyPrefix hT zX B hd₀.2.1
      (Icc_subset_Icc ha hb) hJI hr.le hq
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq]
    apply ENNReal.ofReal_le_ofReal
    exact (pureOccupation_crude_scalar hI.le hh.le hH hp).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))
  apply pureOccupation_of_three (by positivity : 0≤1000000000*H₀^2) hcrude
  · intro hactual
    let m := min p w/128
    let lam := stabilityLength P 16384 M A p w φ
    let len := min I (lam/2)
    have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
    have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hφ
    have hlen : 0<len := lt_min hI (half_pos hlam)
    have hstable : 2*len≤(128*(P/m)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 := by
      have heq : (128*(P/m)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2=lam := by
        dsimp [lam,stabilityLength,stabilityRate,m]
        congr 2
        ring
      rw [heq]
      have hl : len≤lam/2 := min_le_right _ _
      linarith
    have hmw : m≤B.wmin := by
      change min p w/128≤w/8
      have he := min_le_right p w
      linarith
    have hmq : m≤B.qmin := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hwφ : 4≤φ*B.wmin := by
      have hmin : 0 < min p w := lt_min hp hw
      have he := (div_lt_iff₀ hmin).mp hactual
      have he' := mul_le_mul_of_nonneg_left (min_le_right p w) hφ.le
      change 4≤φ*(w/8)
      nlinarith
    have ho := F.closedEulerian_baseline_budget hs.energyPrefix hT zX B hd₀.2.1 (k 0) (k 2)
      (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen (min_le_left _ _) hJI
      hM hA.le hP hL hm hφ (cappedRepresentative_le_one _) (by norm_num : (128:ℝ)≤128)
      hstable le_rfl le_rfl hmq hmw hr hrmax hd le_rfl le_rfl hwφ (HZ zX hzX) HZ
    rw [hs.initial_energy_eq] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact (pureOccupation_stable_scalar hI hh.le hH hp hlam).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))
  · intro hwin
    obtain ⟨hhigh,hlo,hhi⟩ := hwin.min_mass
    have hmq : min p w/128≤B.qmin := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hmw : min p w/128≤B.wmin := by
      change min p w/128≤w/8
      have hh' := min_le_right p w
      linarith
    have ho := himproved s T F hs hT hTT zX B a b (min p w) φ I hzX ha hb hab hJI hmq hmw
      hhigh hlo hhi hr hrmax hd le_rfl le_rfl hsource HZ
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hI₀ : 0<(min p w/P)^2 := sq_pos_of_pos (div_pos (lt_min hp hw) hP)
    exact (pureOccupation_improved_scalar (I:=I) hh.le hH hp hI₀ hφ.le).trans
      (mul_le_mul_of_nonneg_right hKH (by positivity))

end RVM

end

end OAI
