import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SelectionCounts

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma DyadicWindow.mono_width {i k n : ℕ} {x : ℝ} (h : DyadicWindow i n x) (hik : i≤k) :
    DyadicWindow k n x := by
  have hp : (2:ℝ)^i≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hik
  exact ⟨(one_div_le_one_div_of_le (by positivity) hp).trans h.1,h.2.trans hp⟩

lemma jointEnergyBudget_mono_width (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T a b I : ℝ) (n : ℕ×ℕ) {i k : ℕ} (hik : i≤k) :
    jointEnergyBudget s α zX T i a b I n≤jointEnergyBudget s α zX T k a b I n := by
  have hs : sameTimeBudgetSet α zX T i n⊆sameTimeBudgetSet α zX T k n := by
    rintro p ⟨hp,hq,hv⟩
    exact ⟨hp,hq.mono_width hik,hv.mono_width hik⟩
  have ha : arrivalBudgetSet α zX T i n⊆arrivalBudgetSet α zX T k n := by
    rintro p ⟨hq,(⟨hp,hv⟩|⟨hp,hv⟩)⟩
    · exact ⟨hq.mono_width hik,Or.inl ⟨hp,hv.mono_width hik⟩⟩
    · exact ⟨hq.mono_width hik,Or.inr ⟨hp,hv.mono_width hik⟩⟩
  unfold jointEnergyBudget
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro t
  apply lintegral_mono
  intro z
  exact add_le_add (indicator_le_indicator_of_subset hs (by intro; positivity) _)
    (indicator_le_indicator_of_subset ha (by intro; positivity) _)

lemma PhaseFlowOn.closedEulerian_shared_budget {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0≤a) (hb : b≤T) (hlen : 0<len) (hlenI : len≤I) (hab : b-a≤I)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hφ1 : φ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax)
    (hd : B.dmax≤φ^2/32)
    (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2) (hw : 4≤φ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (10240*B.rmax/p)*
        (ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal (I/len)*jointEnergyBudget s F.flow zX T 4
            (max 0 (a-2*I)) (min T (b+I)) I (np,nf)) := by
  have hp0 : 0<p := by rw [hp]; positivity
  have hI : 0<I := hlen.trans_le hlenI
  have hq : 0<B.qmin := (div_pos hp0 (by norm_num)).trans_le hqmin
  let E := ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))
  let J := jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I (np,nf)
  by_cases hrad : B.rmax≤len
  · have ho := F.closedEulerian_stable_budget hs hT zX B hS np nf hp hφeq
      ha hb hlen hM hA hP hL hm hφ hφ1 hconst hstable hqmin hqmax hmq hmw
      hr hrmax hrad hd hDlo hDhi hw HX HZ hI
    have hm := jointEnergyBudget_mono_interval (I:=I) s F.flow zX T 4 (np,nf)
      (stable_source_enlargement (a:=a) (b:=b) (T:=T) hrad hlenI)
    have he : ENNReal.ofReal (40*B.rmax)/ENNReal.ofReal (p/256)=ENNReal.ofReal (10240*B.rmax/p) := by
      rw [←ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      ring
    rw [he,←ENNReal.ofReal_div_of_pos hlen] at ho
    exact ho.trans (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl hm)))
  · by_cases hrI : B.rmax≤I
    · have ho := F.closedBinEulerian_joint_occupation (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin)) hs hT zX B hS np nf
        (Icc_subset_Icc ha hb) (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)) hI hr
        (by rw [hp] at hqmin; linarith) (by rw [hp] at hqmax; linarith)
        (by simpa only [hφeq,inv_pow] using hDlo) (by simpa only [hφeq,inv_pow] using hDhi)
      have hi : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆
          Icc (max 0 (a-2*I)) (min T (b+I)) := by
        apply Icc_subset_Icc
        · exact max_le_max le_rfl (by linarith)
        · exact min_le_min le_rfl (by linarith)
      have hj := (jointEnergyBudget_mono_width s F.flow zX T
        (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (np,nf) (by norm_num : 1≤4)).trans
          (jointEnergyBudget_mono_interval (I:=I) s F.flow zX T 4 (np,nf) hi)
      have ho' := ho.trans (mul_le_mul' le_rfl hj)
      have ho'' := mul_le_mul' (le_refl (ENNReal.ofReal B.qmin)⁻¹) ho'
      rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top,one_mul] at ho''
      have hc : I/B.qmin≤10240*B.rmax/p*(I/len) := by
        calc
          I/B.qmin≤I/(p/128) := div_le_div_of_nonneg_left hI.le (by positivity) hqmin
          _ = 128*I/p := by ring
          _ ≤ 10240*B.rmax/p*(I/len) := by
            have hrl : 1≤B.rmax/len := (le_div_iff₀ hlen).mpr (by linarith [lt_of_not_ge hrad])
            have hc : 128≤10240*(B.rmax/len) := by linarith
            calc
              _=128*(I/p) := by ring
              _≤(10240*(B.rmax/len))*(I/p) := mul_le_mul_of_nonneg_right hc (div_nonneg hI.le hp0.le)
              _=_ := by ring
      calc
        _ ≤ ENNReal.ofReal (I/B.qmin)*J := by
          rw [ENNReal.ofReal_div_of_pos hq]
          simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,J] using ho''
        _ ≤ ENNReal.ofReal (10240*B.rmax/p)* (ENNReal.ofReal (I/len)*J) := by
          rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
        _ ≤ _ := mul_le_mul' le_rfl (le_add_left le_rfl)
    · have ho := F.closedEulerian_crude_budget hs hT zX B hS (Icc_subset_Icc ha hb) hab hr.le hq
      have hc : (I+B.rmax)/B.qmin≤10240*B.rmax/p := by
        calc
          _ ≤ (I+B.rmax)/(p/128) := div_le_div_of_nonneg_left (by positivity) (by positivity) hqmin
          _ ≤ 10240*B.rmax/p := by
            apply (div_le_iff₀ (by positivity : 0<p/128)).mpr
            field_simp
            nlinarith [lt_of_not_ge hrI]
      rw [←ENNReal.ofReal_div_of_pos hq] at ho
      exact ho.trans ((mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl).trans
        (mul_le_mul' le_rfl (le_add_right le_rfl)))

def representativeJointEnergy {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (n : ℕ×ℕ) : ℝ :=
  (jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n).toReal

lemma representativeJointEnergy_nonneg {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (n : ℕ×ℕ) :
    0≤representativeJointEnergy s F zX a b I n := ENNReal.toReal_nonneg

lemma SmoothClassicalPrefix.representativeJointEnergy_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (hI : 0<I) (hab : b-a≤I) :
    Summable (representativeJointEnergy s F zX a b I) ∧
      (∑'n,representativeJointEnergy s F zX a b I n)≤3468*datumEnergyNumber d ∧
    ∀n,jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n=
      ENNReal.ofReal (representativeJointEnergy s F zX a b I n) := by
  have h := F.stable_small_jointBudget_uniform hs.energyPrefix zX hI hab
  rw [hs.initial_energy_eq] at h
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reducePow,Nat.cast_ofNat] at h
  have hc : (867:ℝ≥0∞)*ENNReal.ofReal 4*ENNReal.ofReal (datumEnergyNumber d)=
      ENNReal.ofReal (3468*datumEnergyNumber d) := by
    rw [←ENNReal.ofReal_ofNat (n:=867),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤867),
      ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤867*4)]
    congr 1
    ring
  rw [hc] at h
  have hf := ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  have hn := ENNReal.ne_top_of_tsum_ne_top hf
  refine ⟨ENNReal.summable_toReal hf,?_,fun n=>(ENNReal.ofReal_toReal (hn n)).symm⟩
  change (∑'n,(jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n).toReal)≤_
  rw [←ENNReal.tsum_toReal_eq hn]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg)] at hh

lemma shared_budget_radius_scalar {E J I lam : ℝ} (hE : 0≤E) (hJ : 0≤J)
    (hJE : J≤3468*E) (hI : 0<I) (hlam : 0<lam) :
    E+I/min I (lam/2)*J≤(2+3469*E)*(1+Real.sqrt (I/lam)*Real.sqrt J)^2 := by
  have hratio : I/min I (lam/2)≤1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']; linarith [div_pos hI hlam]
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  have hs : 0≤Real.sqrt (I/lam)*Real.sqrt J := by positivity
  have he : (Real.sqrt (I/lam)*Real.sqrt J)^2=(I/lam)*J := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hJ]
  have hprod := mul_le_mul_of_nonneg_right hratio hJ
  have hpos : 0≤3469*E*(1+Real.sqrt (I/lam)*Real.sqrt J)^2 := by positivity
  nlinarith [sq_nonneg (Real.sqrt (I/lam)*Real.sqrt J),
    mul_nonneg hE hs,mul_nonneg hE (sq_nonneg (Real.sqrt (I/lam)*Real.sqrt J))]

def representativeSharedRadius {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A w a b I : ℝ) (n : ℕ×ℕ) : ℝ :=
  1+Real.sqrt (I/stabilityLength P 16384 M A (sourceRepresentative n.1) w
      (cappedRepresentative n.2))*Real.sqrt (representativeJointEnergy s F zX a b I n)

lemma representativeSharedRadius_one_le {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A w a b I : ℝ) (n : ℕ×ℕ) :
    1≤representativeSharedRadius s F zX P M A w a b I n := by
  unfold representativeSharedRadius
  exact le_add_of_nonneg_right (by positivity)

lemma Admissible.representative_shared_occupation {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      512/min (sourceRepresentative (k 0)) w<cappedRepresentative (k 2) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (C*cappedRepresentative (k 3)/sourceRepresentative (k 0)*
        (representativeSharedRadius s F zX P M A w a b I (k 0,k 2))^2) := by
  let E := datumEnergyNumber d
  let C := 20480*(max 1 T₀)*(2+3469*E)
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hactual HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let m := min p w/128
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let J := representativeJointEnergy s F zX a b I (k 0,k 2)
  let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hHH : H≤ max 1 T₀ := max_le_max le_rfl hTT
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
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
    have hmin : 0< min p w := lt_min hp hw
    have he := (div_lt_iff₀ hmin).mp hactual
    have he' := mul_le_mul_of_nonneg_left (min_le_right p w) hφ.le
    change 4≤φ*(w/8)
    nlinarith
  have hdsmall : B.dmax≤φ^2/32 := by
    have hθ := (cappedRepresentative_pos (k 1)).le
    have hh' := sq_le_sq₀ hθ (by positivity : 0≤φ/16) |>.mpr hsmall
    change 8*(cappedRepresentative (k 1))^2≤φ^2/32
    nlinarith
  have ho := F.closedEulerian_shared_budget hs.energyPrefix hT zX B hd.2.1 (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen (min_le_left _ _) hJI
    hM hA hP hL hm hφ (cappedRepresentative_le_one _) (by norm_num : (128:ℝ)≤128)
    hstable le_rfl le_rfl hmq hmw (representativeClosedBin_radius_pos T w k)
    (by change 0≤2*H*h; positivity) hdsmall le_rfl le_rfl hwφ (HZ zX hzX) HZ
  obtain ⟨hsum,hbudget,hJof⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  have hJ0 : 0≤J := representativeJointEnergy_nonneg _ _ _ _ _ _ _
  have hJE : J≤3468*E := (hsum.le_tsum (k 0,k 2) (fun _ _=>representativeJointEnergy_nonneg _ _ _ _ _ _ _)).trans hbudget
  rw [hs.initial_energy_eq,hJof] at ho
  have hrad := shared_budget_radius_scalar hE hJ0 hJE hI hlam
  change E+I/len*J≤(2+3469*E)*R^2 at hrad
  rw [←ENNReal.ofReal_mul (by positivity : 0≤I/len),
    ←ENNReal.ofReal_add hE (by positivity),←ENNReal.ofReal_mul (by change 0≤10240*(2*H*h)/p; positivity : 0≤10240*B.rmax/p)] at ho
  apply ho.trans
  apply ENNReal.ofReal_le_ofReal
  change 10240*(2*H*h)/p*(E+I/len*J)≤C*h/p*R^2
  calc
    _≤10240*(2*H*h)/p*((2+3469*E)*R^2) := mul_le_mul_of_nonneg_left hrad (by positivity)
    _=(20480*H*(2+3469*E))*h/p*R^2 := by ring
    _≤_ := by dsimp [C]; gcongr

def representativeCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b)

def representativeSpatialCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cappedRepresentative (k 2)/cappedRepresentative (k 1))*
    representativeCentralCost s F zX w k a b

lemma central_near_scalar {C I H h p θ φ : ℝ} :
    (128*C*p^3*θ^2)*(I*(2*H*h-H*h/2)*(384*φ^2))=
      (73728*C*H)*(I*h*p^3*θ^2*φ^2) := by ring

lemma central_far_scalar {C H h p φ R : ℝ} (hC : 0≤C) (hH : 1≤H)
    (hh : 0<h) (hp : 0<p) (hφ : 0<φ) :
    (C*h/p*R^2)/((H*h/2)^2*(φ^2/2))≤(8*C)*(R^2/(p*h*φ^2)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  calc
    _=((8*C)*(R^2/(p*h*φ^2)))/H^2 := by field_simp; ring
    _≤_ := div_le_self (by positivity) (by nlinarith)

lemma Admissible.representative_central_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      512/min (sourceRepresentative (k 0)) w<cappedRepresentative (k 2) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  obtain ⟨Co,hCo,hocc⟩ := hd.representative_shared_occupation T₀
  let C := max (73728*Cρ*max 1 T₀) (8*Co)
  have hC : 0≤C := (by positivity : 0≤73728*Cρ*max 1 T₀).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hactual HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hdiff : 0≤2*H*h-H*h/2 := by nlinarith [mul_nonneg (zero_le_one.trans hH) hh.le]
  have hHH : H≤ max 1 T₀ := max_le_max le_rfl hTT
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)
  have hdensity (t r : ℝ) (n : Sphere) (hr : r∈Icc 0 T) :
      physicalBinDensity s X V B t r n≤ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
    have he := hden s T F hs.energyPrefix hs.initial_f X V B t r n p θ 1 hr hp.le hθ.le
      (by norm_num : (0:ℝ)≤1) (by change p/32≤p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left (show θ≤1 from cappedRepresentative_le_one (k 1))] using he
  have hn := physicalBin_density_near hα.snd.measurable B (J:=Icc a b) measurableSet_Icc hφ.le
    (by rfl : B.Dmax≤8*φ^2) (fun z hz=>hdensity z.1 z.2.1 z.2.2 ⟨hz.2.1.1,hz.2.1.2.trans (hz.1.2.trans hb)⟩)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hf := F.physicalBin_density_far hs.energyPrefix hT zX B hd.2.1 hS0 hJ
    (representativeClosedBin_radius_pos T w k) (by change 0<φ^2/2; positivity)
  have ho := hocc M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hactual HZ
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hn.trans
    calc
      _≤ENNReal.ofReal (128*Cρ*p^3*θ^2)*
          (ENNReal.ofReal I*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
        apply mul_le_mul' le_rfl
        apply mul_le_mul' _ le_rfl
        apply mul_le_mul' _ le_rfl
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_le_ofReal hJI
      _=ENNReal.ofReal ((73728*Cρ*H)*(I*h*p^3*θ^2*φ^2)) := by
        change ENNReal.ofReal (128*Cρ*p^3*θ^2)*
          (ENNReal.ofReal I*ENNReal.ofReal (2*H*h-H*h/2)*ENNReal.ofReal (384*φ^2))=_
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le hdiff),
          ←ENNReal.ofReal_mul (by positivity : 0≤128*Cρ*p^3*θ^2)]
        exact congrArg ENNReal.ofReal central_near_scalar
      _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hHH (by positivity)).trans (le_max_left _ _)) (by positivity))
  · apply hf.trans ((ENNReal.div_le_div_right ho _).trans ?_)
    change ENNReal.ofReal (Co*h/p*R^2)/ENNReal.ofReal ((H*h/2)^2*(φ^2/2))≤_
    rw [←ENNReal.ofReal_div_of_pos (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact (central_far_scalar hCo hH hh hp hφ).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

lemma central_shared_radial_sum {I R p θ φ : ℝ}
    (hI : 0<I) (hR : 0<R) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) :
    (∑'n : ℕ,ENNReal.ofReal (min (I*cappedRepresentative n*p^3*θ^2*φ^2)
      (R^2/(p*cappedRepresentative n*φ^2))))≤
      ENNReal.ofReal (6*Real.sqrt I*R*p*θ) := by
  let g : ℤ→ℝ := fun k=>min (I*p^3*θ*φ^4*((2:ℝ)^k)) (R^2/(p*θ*((2:ℝ)^k)))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := geometry_radial_balance hI hR hp hθ hφ (by norm_num : (0:ℝ)<1)
  simp only [one_mul] at hg
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  have hscale (h : ℝ) (hh : 0<h) :
      min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))=
      (θ/φ^2)*min (I*p^3*θ*φ^4*h) (R^2/(p*θ*h)) := by
    rw [mul_min_of_nonneg _ _ (by positivity : 0≤θ/φ^2)]
    congr 1 <;> field_simp
  simp_rw [hscale _ (cappedRepresentative_pos _),ENNReal.ofReal_mul (by positivity : 0≤θ/φ^2),he]
  rw [ENNReal.tsum_mul_left]
  calc
    _≤ENNReal.ofReal (θ/φ^2)*(∑'k : ℤ,ENNReal.ofReal (g k)) :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (g k)))
    _=ENNReal.ofReal (θ/φ^2)*ENNReal.ofReal (∑'k : ℤ,g k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg.1]
    _≤ENNReal.ofReal (θ/φ^2)*ENNReal.ofReal (6*Real.sqrt I*R*p*φ^2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg.2)
    _=ENNReal.ofReal (6*Real.sqrt I*R*p*θ) := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤θ/φ^2)]
      congr 1
      field_simp

lemma capped_linear_tail_sum {φ : ℝ} (hφ : 0<φ) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))≤
      ENNReal.ofReal (2*φ) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤φ)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))=
      ∑n∈U,ENNReal.ofReal (cappedRepresentative n) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>(cappedRepresentative_pos n).le)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hφ (by norm_num : (0:ℝ)<1) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num only [Real.rpow_one] at hh
  exact hh

lemma Admissible.representative_central_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      512/min (sourceRepresentative np) w<cappedRepresentative nf →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nf
      let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
        representativeCentralCost s F zX w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt I*R*p*φ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd.representative_central_shared T₀
  refine ⟨12*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw hactual HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hr (nt : ℕ) (hnt : cappedRepresentative nt≤φ/16) :
      (∑'nr : ℕ,representativeCentralCost s F zX w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*(6*Real.sqrt I*R*p*cappedRepresentative nt)) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hnt hactual HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤ENNReal.ofReal C*ENNReal.ofReal (6*Real.sqrt I*R*p*cappedRepresentative nt) :=
        mul_le_mul' le_rfl (central_shared_radial_sum hI hR hp (cappedRepresentative_pos _) hφ)
      _=_ := (ENNReal.ofReal_mul hC).symm
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
      representativeCentralCost s F zX w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (6*C*Real.sqrt I*R*p)*
        (∑'nt : ℕ,ENNReal.ofReal (if cappedRepresentative nt≤φ then cappedRepresentative nt else 0)) := by
    rw [←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro nt
    by_cases ht : cappedRepresentative nt≤φ/16
    · have ht' : cappedRepresentative nt≤φ := ht.trans (by linarith)
      simp only [ite_eq_left ht,ite_eq_left ht']
      apply (hr nt ht).trans_eq
      rw [←ENNReal.ofReal_mul (by positivity : 0≤6*C*Real.sqrt I*R*p)]
      congr 1
      ring
    · simp only [ite_eq_right ht,tsum_zero]
      exact bot_le
  apply hsum.trans
  calc
    _≤ENNReal.ofReal (6*C*Real.sqrt I*R*p)*ENNReal.ofReal (2*φ) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul (by positivity : 0≤6*C*Real.sqrt I*R*p)]; congr 1; ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.central_actual_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        512/min (sourceRepresentative n.1) w<cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_central_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    512/min (sourceRepresentative n.1) w<cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := by
    refine ⟨hn.1,?_⟩
    calc
      _≤512/sourceRepresentative n.1 := div_le_div_of_nonneg_right (by norm_num) (hp _).le
      _≤512/min (sourceRepresentative n.1) w := div_le_div_of_nonneg_left (by norm_num) (lt_min (hp _) hw) (min_le_left _ _)
      _≤_ := hn.2.le
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P hM hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw (hU n hn).2 HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn hCc
      simpa only [mul_assoc] using hh)

end RVM

end

end OAI
