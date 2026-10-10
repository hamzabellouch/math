import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SharedOccupation

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_joint_large_budget {s : Solution}
    {T a b φ p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0≤a) (hb : b≤T) (hlen : 0<len) (hlenI : len≤I) (hab : b-a≤I)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hlarge : len<B.rmax)
    (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2) :
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
  by_cases hrI : B.rmax≤I
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
          have hrl : 1≤B.rmax/len := (le_div_iff₀ hlen).mpr (by linarith [hlarge])
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

lemma Admissible.representative_large_shared_occupation {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
        (cappedRepresentative (k 2)))<cappedRepresentative (k 3) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (C*cappedRepresentative (k 3)/sourceRepresentative (k 0)*
        (representativeSharedRadius s F zX P M A w a b I (k 0,k 2))^2) := by
  let E := datumEnergyNumber d
  let C := 20480*(max 1 T₀)*(2+3469*E)
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hlarge
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
  have hlenr : len<B.rmax := by
    have hl : len ≤ min I lam := min_le_min le_rfl (by linarith)
    have hr0 : h≤2*H*h := by nlinarith
    exact (hl.trans_lt hlarge).trans_le hr0
  have ho := F.closedEulerian_joint_large_budget hs.energyPrefix hT zX B hd.2.1 (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen (min_le_left _ _) hJI
    le_rfl le_rfl (representativeClosedBin_radius_pos T w k)
    (by change 0≤2*H*h; positivity) hlenr le_rfl le_rfl
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

lemma Admissible.representative_central_large_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
        (cappedRepresentative (k 2)))<cappedRepresentative (k 3) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  obtain ⟨Co,hCo,hocc⟩ := hd.representative_large_shared_occupation T₀
  let C := max (73728*Cρ*max 1 T₀) (8*Co)
  have hC : 0≤C := (by positivity : 0≤73728*Cρ*max 1 T₀).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hlarge HZ
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
  have ho := hocc M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hlarge
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

def regularCentralIndex (P M A I w : ℝ) (k : Fin 4→ℕ) : Prop :=
  512/min (sourceRepresentative (k 0)) w<cappedRepresentative (k 2) ∨
  min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
    (cappedRepresentative (k 2)))<cappedRepresentative (k 3)

noncomputable def representativeRegularCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then representativeCentralCost s F zX w k a b else 0

lemma Admissible.representative_regular_central_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeRegularCentralCost s F zX P M A I w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  classical
  obtain ⟨Ca,hCa,ha⟩ := hd.representative_central_shared T₀
  obtain ⟨Cr,hCr,hr⟩ := hd.representative_central_large_shared T₀
  refine ⟨max Ca Cr,hCa.trans (le_max_left _ _),?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall HZ
  dsimp only
  unfold representativeRegularCentralCost
  split_ifs with h
  · rcases h with h|h
    · apply (ha M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall h HZ).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      exact le_min (by dsimp [sourceRepresentative,cappedRepresentative]; positivity) (by dsimp [sourceRepresentative,cappedRepresentative]; positivity)
    · apply (hr M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall h HZ).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      exact le_min (by dsimp [sourceRepresentative,cappedRepresentative]; positivity) (by dsimp [sourceRepresentative,cappedRepresentative]; positivity)
  · exact bot_le

lemma capped_square_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))≤
      ENNReal.ofReal (2*x^2) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))=
      ∑n∈U,ENNReal.ofReal ((cappedRepresentative n)^2) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<2) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num at hh
  nlinarith [sq_nonneg x]

lemma capped_fourth_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^4 else 0))≤
      ENNReal.ofReal (2*x^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^4 else 0))=
      ∑n∈U,ENNReal.ofReal ((cappedRepresentative n)^4) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<4) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num at hh
  nlinarith [sq_nonneg (x^2)]

lemma small_deficit_stabilityLength {P M A p w φ : ℝ}
    (hP : 0<P) (hM : 1≤M) (hp : 0<p) (hw : 0<w) (hφ : 0<φ)
    (hsmall : φ≤512/min p w) : stabilityLength P 16384 M A p w φ≤1/P^2 := by
  have hm : 0 < min p w := lt_min hp hw
  have hprod : min p w*φ≤512 := by
    have hh := (le_div_iff₀ hm).mp hsmall
    nlinarith
  have hPr : P ≤ stabilityRate P 16384 M A p w φ := by
    have he : 16384*(P/min p w)*(M/φ)=(16384*P*M)/(min p w*φ) := by field_simp
    calc
      P≤(16384*P*M)/(min p w*φ) := by
        apply (le_div_iff₀ (mul_pos hm hφ)).mpr
        have hh := mul_le_mul_of_nonneg_left hprod hP.le
        have hM' := mul_le_mul_of_nonneg_left hM (by positivity : 0≤16384*P)
        nlinarith
      _=16384*(P/min p w)*(M/φ) := he.symm
      _≤_ := by
        unfold stabilityRate
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (by positivity)
  have hi := one_div_le_one_div_of_le hP hPr
  have hr : 0 < stabilityRate P 16384 M A p w φ := hP.trans_le hPr
  have hh := pow_le_pow_left₀ (by positivity : 0≤1/stabilityRate P 16384 M A p w φ) hi 2
  simpa only [stabilityLength,one_div,inv_pow] using hh

lemma central_exception_coefficient {P p w : ℝ} (hP : 1≤P) (hp : 1≤p)
    (hpP : p≤P) (hw : 1≤w) (hwP : w≤P) :
    p^3/P^2*(512/min p w)^4≤2*512^4*P^2/w := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP2 : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  have hP4 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (by decide : 1≤4)
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    have he : p^3/P^2*(512/p)^4=512^4/(P^2*p) := by field_simp
    rw [he]
    have hden : w≤P^4*p := hwP.trans (hP4.trans
      (le_mul_of_one_le_right (pow_nonneg hP0.le 4) hp))
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hP0) hp0) hw0).mpr
    have hh := mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ)≤512^4)
    have ht : 0≤512^4*P^4*p := by positivity
    nlinarith only [hh,ht]
  · rw [min_eq_right hwp]
    have hp3 : p^3/P^2≤P := by
      apply (div_le_iff₀ (sq_pos_of_pos hP0)).mpr
      nlinarith only [pow_le_pow_left₀ hp0.le hpP 3]
    have hww : w≤w^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hw (by decide : 1≤4)
    calc
      _≤P*(512/w)^4 := mul_le_mul_of_nonneg_right hp3 (by positivity)
      _=512^4*(P/w^4) := by ring
      _≤512^4*(P/w) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hP0.le hw0 hww) (by norm_num)
      _≤512^4*(P^2/w) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hP2 hw0.le) (by norm_num)
      _≤_ := by
        have ht : 0≤512^4*(P^2/w) := by positivity
        calc
          _≤2*(512^4*(P^2/w)) := by linarith only [ht]
          _=_ := by ring

lemma capped_cube_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^3 else 0))≤
      ENNReal.ofReal (2*x^3) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^3 else 0))=
      ∑n∈U,ENNReal.ofReal ((cappedRepresentative n)^3) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>pow_nonneg (cappedRepresentative_pos n).le 3)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<3) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num at hh
  nlinarith [pow_nonneg hx.le 3]

lemma magnetic_low_radial_sum {I p θ φ : ℝ} (hI : 0<I) (hp : 0<p) :
    (∑'nr : ℕ,if cappedRepresentative nr≤I then
      ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*θ^2*φ) else 0)≤
      ENNReal.ofReal ((I*p^2*θ^2*φ)*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  have hh := majorant_capped_short_sqrt_radius_sum (by norm_num : (0:ℝ)<1) hI
    (K:=max 0 (I*p^2*θ^2*φ)) (le_max_left _ _)
  by_cases hφ : 0≤φ
  · rw [max_eq_right (by positivity : 0≤I*p^2*θ^2*φ)] at hh
    simpa only [one_mul,show ∀r : ℝ,(I*p^2*θ^2*φ)*Real.sqrt r=I*Real.sqrt r*p^2*θ^2*φ from by intro r; ring] using hh
  · have hφ' : φ≤0 := le_of_not_ge hφ
    have hz (nr : ℕ) : ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*θ^2*φ)=0 :=
      ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hφ')
    simp only [hz,ite_self,tsum_zero,zero_le]

lemma magnetic_low_angle_radial_sum {I p φ : ℝ} (hI : 0<I) (hp : 0<p) (hφ : 0<φ) :
    (∑'nt : ℕ,if cappedRepresentative nt≤φ then ∑'nr : ℕ,
      if cappedRepresentative nr≤I then
        ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*φ) else 0 else 0)≤
      ENNReal.ofReal (2*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*I*Real.sqrt I*p^2*φ^3) := by
  classical
  let K := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hK : 0<K := majorant_shortSqrtConstant_pos
  have hC : 0≤I*p^2*φ*K*Real.sqrt I := by positivity
  calc
    _≤∑'nt : ℕ,if cappedRepresentative nt≤φ then
        ENNReal.ofReal ((I*p^2*(cappedRepresentative nt)^2*φ)*K*Real.sqrt I) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      split_ifs
      · exact magnetic_low_radial_sum hI hp
      · rfl
    _=ENNReal.ofReal (I*p^2*φ*K*Real.sqrt I)*
        (∑'nt : ℕ,ENNReal.ofReal (if cappedRepresentative nt≤φ then (cappedRepresentative nt)^2 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nt
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
      congr 1
      ring
    _≤ENNReal.ofReal (I*p^2*φ*K*Real.sqrt I)*ENNReal.ofReal (2*φ^2) :=
      mul_le_mul' le_rfl (capped_square_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma magnetic_low_triple_sum {I p w : ℝ} (hI : 0<I) (hp : 0<p) (hw : 0<w) :
    (∑'nf : ℕ, if cappedRepresentative nf≤512/min p w then
      ∑'nt : ℕ, if cappedRepresentative nt≤cappedRepresentative nf then ∑'nr : ℕ,
        if cappedRepresentative nr≤I then
          ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
        else 0 else 0 else 0)≤
      ENNReal.ofReal (4*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*I*Real.sqrt I*p^2*(512/min p w)^3) := by
  classical
  have hm : 0 < min p w := lt_min hp hw
  let K := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hK : 0<K := majorant_shortSqrtConstant_pos
  have hC : 0≤2*K*I*Real.sqrt I*p^2 := by positivity
  calc
    _≤∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ENNReal.ofReal (2*K*I*Real.sqrt I*p^2*(cappedRepresentative nf)^3) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs
      · exact magnetic_low_angle_radial_sum hI hp (cappedRepresentative_pos _)
      · rfl
    _=ENNReal.ofReal (2*K*I*Real.sqrt I*p^2)*
        (∑'nf : ℕ, ENNReal.ofReal (if cappedRepresentative nf≤512/min p w then (cappedRepresentative nf)^3 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nf
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    _≤ENNReal.ofReal (2*K*I*Real.sqrt I*p^2)*ENNReal.ofReal (2*(512/min p w)^3) :=
      mul_le_mul' le_rfl (capped_cube_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma magnetic_low_coefficient {P p w : ℝ} (hP : 1≤P) (hp : 1≤p)
    (hpP : p≤P) (hw : 1≤w) (hwP : w≤P) :
    p^2*(512/min p w)^3≤512^3*P^2/w := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP2 : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    have he : p^2*(512/p)^3=512^3/p := by field_simp
    rw [he]
    apply (div_le_div_iff₀ hp0 hw0).mpr
    have hh : w≤P^2*p := hwP.trans (hP2.trans (le_mul_of_one_le_right (sq_nonneg _) hp))
    nlinarith only [mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤512^3)]
  · rw [min_eq_right hwp]
    have hww : w≤w^3 := by simpa only [pow_one] using pow_le_pow_right₀ hw (by decide : 1≤3)
    calc
      _≤P^2*(512/w)^3 := mul_le_mul_of_nonneg_right (sq_le_sq₀ hp0.le hP0.le |>.mpr hpP) (by positivity)
      _=512^3*(P^2/w^3) := by ring
      _≤512^3*(P^2/w) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) hw0 hww) (by norm_num)
      _=_ := by ring

lemma Admissible.representative_central_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*(I*cappedRepresentative (k 3)*(sourceRepresentative (k 0))^3*
          (cappedRepresentative (k 1))^2*(cappedRepresentative (k 2))^2)) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  refine ⟨73728*Cρ*max 1 T₀,by positivity,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hJI
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
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
  apply hn.trans
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
      (mul_le_mul_of_nonneg_left hHH (by positivity)) (by positivity))

lemma Admissible.representative_regular_central_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nf
      let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
        representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt I*R*p*φ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_central_shared T₀
  refine ⟨12*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hr (nt : ℕ) (hnt : cappedRepresentative nt≤φ/16) :
      (∑'nr : ℕ,representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*(6*Real.sqrt I*R*p*cappedRepresentative nt)) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hnt HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤ENNReal.ofReal C*ENNReal.ofReal (6*Real.sqrt I*R*p*cappedRepresentative nt) :=
        mul_le_mul' le_rfl (central_shared_radial_sum hI hR hp (cappedRepresentative_pos _) hφ)
      _=_ := (ENNReal.ofReal_mul hC).symm
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
      representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
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

lemma Admissible.central_regular_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_central_double_sum T₀
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
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
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
        hzX ha hb hI hJI hw HZ
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

lemma central_exception_radial_sum {P I p θ φ : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) :
    (∑'nr : ℕ, if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal (I*cappedRepresentative nr*p^3*θ^2*φ^2) else 0)≤
      ENNReal.ofReal (2*I*p^3/P^2*θ^2*φ^2) := by
  classical
  have hC : 0≤I*p^3*θ^2*φ^2 := by positivity
  have he (nr : ℕ) : (if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal (I*cappedRepresentative nr*p^3*θ^2*φ^2) else 0)=
      ENNReal.ofReal (I*p^3*θ^2*φ^2)*ENNReal.ofReal
        (if cappedRepresentative nr≤1/P^2 then cappedRepresentative nr else 0) := by
    split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    congr 1
    ring
  simp_rw [he]
  rw [ENNReal.tsum_mul_left]
  calc
    _≤ENNReal.ofReal (I*p^3*θ^2*φ^2)*ENNReal.ofReal (2*(1/P^2)) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma central_exception_angle_radial_sum {P I p φ : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) (hφ : 0<φ) :
    (∑'nt : ℕ, if cappedRepresentative nt≤φ then ∑'nr : ℕ,
      if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2) else 0 else 0)≤
      ENNReal.ofReal (4*I*p^3/P^2*φ^4) := by
  classical
  have hC : 0≤2*I*p^3/P^2*φ^2 := by positivity
  calc
    _≤∑'nt : ℕ, if cappedRepresentative nt≤φ then
        ENNReal.ofReal (2*I*p^3/P^2*(cappedRepresentative nt)^2*φ^2) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      split_ifs
      · exact central_exception_radial_sum hP hI hp
      · rfl
    _=ENNReal.ofReal (2*I*p^3/P^2*φ^2)*
        (∑'nt : ℕ, ENNReal.ofReal (if cappedRepresentative nt≤φ then (cappedRepresentative nt)^2 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nt
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
      congr 1
      ring
    _≤ENNReal.ofReal (2*I*p^3/P^2*φ^2)*ENNReal.ofReal (2*φ^2) :=
      mul_le_mul' le_rfl (capped_square_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma central_exception_triple_sum {P I p w : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) (hw : 0<w) :
    (∑'nf : ℕ, if cappedRepresentative nf≤512/min p w then
      ∑'nt : ℕ, if cappedRepresentative nt≤cappedRepresentative nf then ∑'nr : ℕ,
        if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*(cappedRepresentative nf)^2)
        else 0 else 0 else 0)≤ENNReal.ofReal (8*I*p^3/P^2*(512/min p w)^4) := by
  classical
  have hm : 0 < min p w := lt_min hp hw
  have hC : 0≤4*I*p^3/P^2 := by positivity
  calc
    _≤∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ENNReal.ofReal (4*I*p^3/P^2*(cappedRepresentative nf)^4) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs
      · exact central_exception_angle_radial_sum hP hI hp (cappedRepresentative_pos _)
      · rfl
    _=ENNReal.ofReal (4*I*p^3/P^2)*
        (∑'nf : ℕ,ENNReal.ofReal (if cappedRepresentative nf≤512/min p w then (cappedRepresentative nf)^4 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nf
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    _≤ENNReal.ofReal (4*I*p^3/P^2)*ENNReal.ofReal (2*(512/min p w)^4) :=
      mul_le_mul' le_rfl (capped_fourth_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

noncomputable def representativeExceptionCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then 0 else representativeCentralCost s F zX w k a b

lemma central_cost_eq_regular_add_exception {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) :
    representativeCentralCost s F zX w k a b=
      representativeRegularCentralCost s F zX P M A I w k a b+
      representativeExceptionCentralCost s F zX P M A I w k a b := by
  classical
  simp only [representativeRegularCentralCost,representativeExceptionCentralCost]
  split_ifs <;> simp

lemma Admissible.representative_exception_central_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*(sourceRepresentative np)^3/P^2*(512/min (sourceRepresentative np) w)^4) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_central_near T₀
  refine ⟨8*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if cappedRepresentative nt≤cappedRepresentative nf/16 then
        representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
        if cappedRepresentative nt≤cappedRepresentative nf then
          if cappedRepresentative nr≤1/P^2 then
            ENNReal.ofReal (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*(cappedRepresentative nf)^2)
          else 0 else 0 else 0) := by
    by_cases ht : cappedRepresentative nt≤cappedRepresentative nf/16
    · rw [ite_eq_left ht]
      by_cases hr : regularCentralIndex P M A I w ![np,nt,nf,nr]
      · simp only [representativeExceptionCentralCost,ite_eq_left hr]
        exact bot_le
      · have hreg : ¬(512/min p w<cappedRepresentative nf ∨
            min I (stabilityLength P 16384 M A p w (cappedRepresentative nf))<cappedRepresentative nr) := by
          simpa [regularCentralIndex,p] using hr
        have hf : cappedRepresentative nf≤512/min p w := le_of_not_gt (not_or.mp hreg).1
        have hnr : cappedRepresentative nr≤1/P^2 :=
          ((le_of_not_gt (not_or.mp hreg).2).trans (min_le_right _ _)).trans
            (small_deficit_stabilityLength hP hM hp hw (cappedRepresentative_pos _) hf)
        have hnt : cappedRepresentative nt≤cappedRepresentative nf := by
          have hf0 := (cappedRepresentative_pos nf).le
          linarith
        rw [ite_eq_left hf,ite_eq_left hnt,ite_eq_left hnr,representativeExceptionCentralCost,ite_eq_right hr]
        rw [←ENNReal.ofReal_mul hCn]
        simpa [p] using hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
          if cappedRepresentative nt≤cappedRepresentative nf then
            if cappedRepresentative nr≤1/P^2 then
              ENNReal.ofReal (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*(cappedRepresentative nf)^2)
            else 0 else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ∑'nt : ℕ,if cappedRepresentative nt≤cappedRepresentative nf then
          ∑'nr : ℕ,if cappedRepresentative nr≤1/P^2 then
            ENNReal.ofReal (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*(cappedRepresentative nf)^2)
          else 0 else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro nf
      split_ifs with hf
      · apply tsum_congr
        intro nt
        split_ifs with ht <;> simp only [tsum_zero]
      · simp only [tsum_zero]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (8*I*p^3/P^2*(512/min p w)^4) :=
      mul_le_mul' le_rfl (central_exception_triple_sum hP hI.le hp hw)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring

lemma sourceRepresentative_one_le (n : ℕ) : 1 ≤ sourceRepresentative n := by
  have h : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  dsimp [sourceRepresentative]
  nlinarith only [h]

lemma Admissible.central_exception_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_exception_central_triple_sum T₀
  have hpc := pairCountConstant_pos
  refine ⟨2*512^4*Cn*pairCountConstant,by positivity,?_⟩
  intro M A P hM hP hL s T F hs hT hTT zX a b I w ha hb hI hJI hw hwP
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative nf/16 then
      representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0
  let D := 2*512^4*Cn*I*P^2/w
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hD : 0≤D := by dsimp [D]; positivity
  have hgb (np : ℕ) (hn : sourceRepresentative np≤P) : g np≤ENNReal.ofReal D := by
    apply (hnear M A P hM hP0 s T F hs hT hTT zX np a b I w ha hb hI hJI hw0).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left
      (central_exception_coefficient hP (sourceRepresentative_one_le _) hn hw hwP)
      (mul_nonneg hCn hI.le)
    calc
      _=(Cn*I)*((sourceRepresentative np)^3/P^2*(512/min (sourceRepresentative np) w)^4) := by ring
      _≤(Cn*I)*(2*512^4*P^2/w) := hh
      _=D := by dsimp [D]; ring
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have hsub : U⊆Finset.range N := by
    intro np hn
    have hpn : 1/sourceRepresentative np≤cappedRepresentative 0 := by
      rw [show cappedRepresentative 0=1 by rfl]
      exact (div_le_one (zero_lt_one.trans_le (sourceRepresentative_one_le _))).mpr (sourceRepresentative_one_le _)
    exact Finset.mem_range.mpr (hidx np 0 (hU np hn) hpn).1
  have hcard : (U.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
    have hh : (U.card:ℝ)≤N := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
    exact hh.trans hN
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal D := Finset.sum_le_sum (fun np hn=>hgb np (hU np hn))
    _=ENNReal.ofReal ((U.card:ℝ)*D) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hD)]
      simp
    _≤ENNReal.ofReal ((pairCountConstant*Real.log (2+P))*D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hD)
    _=_ := by congr 1; dsimp [D]; ring

lemma Admissible.representative_spatial_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      representativeSpatialCost s F zX w k a b≤
        ENNReal.ofReal (C*(I*cappedRepresentative (k 3)*(sourceRepresentative (k 0))^3*
          cappedRepresentative (k 1)*(cappedRepresentative (k 2))^3)) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_central_near T₀
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hJI
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  apply (mul_le_mul' le_rfl (hbound s T F hs hT hTT zX k a b I w ha hb hI hJI)).trans
  rw [←ENNReal.ofReal_mul (by positivity : 0≤cappedRepresentative (k 2)/cappedRepresentative (k 1))]
  apply le_of_eq
  congr 1
  field_simp

lemma Admissible.representative_spatial_regular_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      regularCentralIndex P M A I w k →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeSpatialCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ*φ^3) (R^2/(p*h*θ*φ))) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_central_shared T₀
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hreg HZ
  dsimp only
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hbnd := hbound M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall HZ
  dsimp only at hbnd
  rw [representativeRegularCentralCost,ite_eq_left hreg] at hbnd
  apply (mul_le_mul' le_rfl hbnd).trans
  rw [←ENNReal.ofReal_mul (by positivity : 0≤cappedRepresentative (k 2)/cappedRepresentative (k 1))]
  apply le_of_eq
  congr 1
  rw [show cappedRepresentative (k 2)/cappedRepresentative (k 1)*
    (C*min _ _) = C*((cappedRepresentative (k 2)/cappedRepresentative (k 1))*min _ _) by ring,
    mul_min_of_nonneg _ _ (by positivity : 0≤cappedRepresentative (k 2)/cappedRepresentative (k 1))]
  congr 2 <;> field_simp

lemma Admissible.representative_spatial_pure_far {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeSpatialCost s F zX w k a b≤
        ENNReal.ofReal (C*pureOccupationEnvelope P 512 16384 M A p w φ h I/(h^2*θ*φ)) := by
  let E := datumEnergyNumber d
  let K := 1000000000*(max 1 T₀)^2
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨8*K*E,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hd.representative_pure_occupation T₀ M A hM hA] with P hoccup
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let μ := pureOccupationEnvelope P 512 16384 M A p w φ h I
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hμ : 0≤μ := pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI.le
  have hf := F.physicalBin_density_far hs.energyPrefix hT zX B hd.2.1
    (show tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ by
      have h0 : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
      rw [h0])
    (Icc_subset_Icc ha hb) (representativeClosedBin_radius_pos T w k)
    (by change 0<φ^2/2; positivity)
  have ho := hoccup s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  change _≤ENNReal.ofReal (K*μ)*ENNReal.ofReal E at ho
  have hD : 0<(H*h)^2*φ^2/8 := by positivity
  change representativeCentralCost s F zX w k a b≤
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
        (max 0 (a-B.rmax)) (min T (b-B.rmin)))/ENNReal.ofReal ((H*h/2)^2*(φ^2/2)) at hf
  have he : (H*h/2)^2*(φ^2/2)=(H*h)^2*φ^2/8 := by ring
  rw [he] at hf
  apply (mul_le_mul' le_rfl (hf.trans (ENNReal.div_le_div_right ho _))).trans
  rw [←ENNReal.ofReal_mul (mul_nonneg hK hμ),←ENNReal.ofReal_div_of_pos hD,
    ←ENNReal.ofReal_mul (div_nonneg hφ.le hθ.le)]
  apply ENNReal.ofReal_le_ofReal
  change (φ/θ)*(K*μ*E/((H*h)^2*φ^2/8))≤(8*K*E)*μ/(h^2*θ*φ)
  calc
    _=((8*K*E)*μ/(h^2*θ*φ))/H^2 := by field_simp
    _≤(8*K*E)*μ/(h^2*θ*φ) := div_le_self (by positivity) (by nlinarith [sq_nonneg (H-1)])

lemma near_threshold_spatial {I h p θ φ P W : ℝ}
    (hI : 0<I) (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (_ : 0≤P) (_ : 0≤W)
    (hnear : I*Real.sqrt h*p^2*φ^2≤P*Real.sqrt I*W) :
    I*h*p^3*θ*φ^3≤P^2*W^2*θ/(p*φ) := by
  have hsI : 0<Real.sqrt I := Real.sqrt_pos.mpr hI
  have hs : Real.sqrt I*Real.sqrt h*p^2*φ^2≤P*W := by
    apply (mul_le_mul_iff_right₀ hsI).mp
    calc
      _=I*Real.sqrt h*p^2*φ^2 := by
        calc
          _=(Real.sqrt I)^2*Real.sqrt h*p^2*φ^2 := by ring
          _=_ := by rw [Real.sq_sqrt hI.le]
      _≤P*Real.sqrt I*W := hnear
      _=_ := by ring
  have hsq := pow_le_pow_left₀ (by positivity : 0≤Real.sqrt I*Real.sqrt h*p^2*φ^2) hs 2
  have he : (Real.sqrt I*Real.sqrt h*p^2*φ^2)^2=I*h*p^4*φ^4 := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hI.le,Real.sq_sqrt hh.le]
    ring
  rw [he] at hsq
  apply (le_div_iff₀ (mul_pos hp hφ)).mpr
  have hh' := mul_le_mul_of_nonneg_left hsq hθ.le
  nlinarith only [hh']

lemma far_threshold_spatial {I h p θ φ μ P W : ℝ}
    (hI : 0<I) (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hμ : 0≤μ) (_ : 0≤P) (_ : 0≤W)
    (hfar : Real.sqrt I*Real.sqrt (p*μ)/(θ*h)≤P*Real.sqrt I*W) :
    μ/(h^2*θ*φ)≤P^2*W^2*θ/(p*φ) := by
  have hsI : 0<Real.sqrt I := Real.sqrt_pos.mpr hI
  have hs : Real.sqrt (p*μ)≤P*W*θ*h := by
    apply (mul_le_mul_iff_right₀ hsI).mp
    calc
      _=(Real.sqrt I*Real.sqrt (p*μ)/(θ*h))*(θ*h) := by field_simp
      _≤(P*Real.sqrt I*W)*(θ*h) := mul_le_mul_of_nonneg_right hfar (mul_nonneg hθ.le hh.le)
      _=_ := by ring
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (p*μ)) hs 2
  rw [Real.sq_sqrt (mul_nonneg hp.le hμ)] at hsq
  have hden : 0<h^2*θ*φ := by positivity
  apply (div_le_div_iff₀ hden (mul_pos hp hφ)).mpr
  have hh' := mul_le_mul_of_nonneg_left hsq hφ.le
  nlinarith only [hh']

lemma unselected_spatial_cap {I h p θ φ μ P W : ℝ}
    (hI : 0<I) (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hμ : 0≤μ) (hP : 0≤P) (hW : 0≤W)
    (hfail : ¬ P*Real.sqrt I*W < min (I*Real.sqrt h*p^2*φ^2)
      (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    min (I*h*p^3*θ*φ^3) (μ/(h^2*θ*φ))≤P^2*W^2*θ/(p*φ) := by
  rcases min_le_iff.mp (le_of_not_gt hfail) with hn|hf
  · exact (min_le_left _ _).trans (near_threshold_spatial hI hh hp hθ hφ hP hW hn)
  · exact (min_le_right _ _).trans (far_threshold_spatial hI hh hp hθ hφ hμ hP hW hf)

lemma Admissible.unselected_spatial_polynomial_cap {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      ¬ representativeSelected P M A w I k →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeSpatialCost s F zX w k a b≤
        ENNReal.ofReal (C*(P^2*(selectionWeight P θ φ h)^2*θ/(p*φ))) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_spatial_near T₀
  obtain ⟨Cf,hCf,hfar⟩ := hd.representative_spatial_pure_far T₀
  let C := max Cn Cf
  have hC : 0≤C := hCn.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hfar M A hM hA,eventually_gt_atTop (0:ℝ)] with P hf hP
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hfail hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let μ := pureOccupationEnvelope P 512 16384 M A p w φ h I
  let W := selectionWeight P θ φ h
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hμ : 0≤μ := pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI.le
  have hW : 0≤W := by dsimp [W,selectionWeight]; positivity
  have hn := hnear s T F hs hT hTT zX k a b I w ha hb hI hJI
  have hff := hf s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only at hff
  have hn' : representativeSpatialCost s F zX w k a b≤ENNReal.ofReal (C*(I*h*p^3*θ*φ^3)) :=
    hn.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hf' : representativeSpatialCost s F zX w k a b≤ENNReal.ofReal (C*(μ/(h^2*θ*φ))) := by
    apply hff.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _=Cf*(μ/(h^2*θ*φ)) := by ring
      _≤_ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hcap := unselected_spatial_cap hI hh hp hθ hφ hμ hP.le hW hfail
  calc
    _ ≤ min (ENNReal.ofReal (C*(I*h*p^3*θ*φ^3))) (ENNReal.ofReal (C*(μ/(h^2*θ*φ)))) :=
      le_min hn' hf'
    _=ENNReal.ofReal (C*min (I*h*p^3*θ*φ^3) (μ/(h^2*θ*φ))) := by
      rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
    _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcap hC)

lemma Admissible.central_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cr,hCr,hregular⟩ := hd.central_regular_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.central_exception_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let Gr := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0
  let Ge := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0
  have he (n : ℕ×ℕ) : Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n=
      Q.indicator Gr n+Q.indicator Ge n := by
    by_cases hn : n∈Q
    · simp only [indicator_of_mem hn,Gr,Ge]
      rw [←ENNReal.tsum_add]
      apply tsum_congr
      intro nt
      rw [←ENNReal.tsum_add]
      apply tsum_congr
      intro nr
      split_ifs
      · exact central_cost_eq_regular_add_exception ..
      · simp
    · simp only [indicator_of_notMem hn,zero_add]
  change (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeCentralCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤_
  simp_rw [he]
  rw [ENNReal.tsum_add]
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := I*P^2*Real.log (2+P)/w
  have hV : 0≤V := by dsimp [V]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hVB : V≤B := by
    have hroot := Real.sqrt_nonneg A
    have hfirst : 0≤P*Real.sqrt I := by positivity
    have ht : V≤(M+Real.sqrt A)*V := le_mul_of_one_le_left hV (by linarith)
    calc
      V≤(M+Real.sqrt A)*V := ht
      _≤P*Real.sqrt I+(M+Real.sqrt A)*V := le_add_of_nonneg_left hfirst
      _=B := by dsimp [B,V]; ring
  have hr := hregular M A P (zero_lt_one.trans_le hM) hA hP hL s T F hs hT hTT
    zX a b I w hzX ha hb hI hJI (zero_lt_one.trans_le hw) hwP HZ
  have he' := hexception M A P hM hP hL s T F hs hT hTT zX a b I w ha hb hI hJI hw hwP
  calc
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hr he'
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=ENNReal.ofReal ((Cr+Ce)*B) := by rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]; congr 1; ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_transport_near_point {θ φ σ : ℝ} (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0≤σ)
    (hφθ : φ≤16*θ) :
    (min θ σ)^2*φ^2*(θ+φ)/θ^3≤17*σ*φ^2/θ := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hs : (min θ σ)^2≤θ*σ := by
    calc
      _=(min θ σ)*(min θ σ) := pow_two _
      _≤θ*σ := mul_le_mul (min_le_left _ _) (min_le_right _ _) hν hθ.le
  calc
    _≤(θ*σ)*φ^2*(17*θ)/θ^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_right hs (sq_nonneg φ)) (by linarith : θ+φ≤17*θ)
        (by positivity) (by positivity)
    _=_ := by field_simp

lemma remaining_transport_near_angular :
    (∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16*cappedRepresentative nt then
      ∑'j : ℕ,ENNReal.ofReal ((min (cappedRepresentative nt) (cappedRepresentative j))^2*
        (cappedRepresentative nf)^2*(cappedRepresentative nt+cappedRepresentative nf)/(cappedRepresentative nt)^3)
      else 0)≤ENNReal.ofReal 34816 := by
  have hrelative (nt nf : ℕ) (hφθ : cappedRepresentative nf≤16*cappedRepresentative nt) :
      (∑'j : ℕ,ENNReal.ofReal ((min (cappedRepresentative nt) (cappedRepresentative j))^2*
        (cappedRepresentative nf)^2*(cappedRepresentative nt+cappedRepresentative nf)/(cappedRepresentative nt)^3))≤
      ENNReal.ofReal (34*(cappedRepresentative nf)^2/cappedRepresentative nt) := by
    calc
      _≤∑'j : ℕ,ENNReal.ofReal ((17*(cappedRepresentative nf)^2/cappedRepresentative nt)*cappedRepresentative j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        apply ENNReal.ofReal_le_ofReal
        calc
          _≤17*cappedRepresentative j*(cappedRepresentative nf)^2/cappedRepresentative nt :=
            remaining_transport_near_point (cappedRepresentative_pos _) (cappedRepresentative_pos _).le
              (cappedRepresentative_pos _).le hφθ
          _=_ := by ring
      _=_ := by
        rw [show (∑'j : ℕ,ENNReal.ofReal ((17*(cappedRepresentative nf)^2/cappedRepresentative nt)*cappedRepresentative j))=
          ∑'j : ℕ,ENNReal.ofReal ((17*(cappedRepresentative nf)^2/cappedRepresentative nt)*(1*cappedRepresentative j)) by simp]
        rw [capped_linear_radius_sum (div_nonneg (by positivity) (cappedRepresentative_pos _).le) (by norm_num)]
        congr 1
        ring
  have hreceiver (nt : ℕ) :
      (∑'nf : ℕ,if cappedRepresentative nf≤16*cappedRepresentative nt then
        ENNReal.ofReal (34*(cappedRepresentative nf)^2/cappedRepresentative nt) else 0)≤
      ENNReal.ofReal (17408*cappedRepresentative nt) := by
    let θ := cappedRepresentative nt
    have hθ : 0<θ := cappedRepresentative_pos _
    have he (nf : ℕ) : (if cappedRepresentative nf≤16*θ then
        ENNReal.ofReal (34*(cappedRepresentative nf)^2/θ) else 0)=
        ENNReal.ofReal (34/θ)*ENNReal.ofReal (if cappedRepresentative nf≤16*θ then (cappedRepresentative nf)^2 else 0) := by
      split_ifs
      · rw [←ENNReal.ofReal_mul (by positivity : 0≤34/θ)]
        congr 1
        ring
      · simp
    change (∑'nf : ℕ,if cappedRepresentative nf≤16*θ then ENNReal.ofReal (34*(cappedRepresentative nf)^2/θ) else 0)≤_
    simp_rw [he]
    rw [ENNReal.tsum_mul_left]
    calc
      _≤ENNReal.ofReal (34/θ)*ENNReal.ofReal (2*(16*θ)^2) :=
        mul_le_mul' le_rfl (capped_square_tail_sum (by positivity))
      _=_ := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤34/θ)]
        congr 1
        dsimp [θ]
        field_simp
        ring
  calc
    _≤∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16*cappedRepresentative nt then
        ENNReal.ofReal (34*(cappedRepresentative nf)^2/cappedRepresentative nt) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs with h
      · exact hrelative nt nf h
      · rfl
    _≤∑'nt : ℕ,ENNReal.ofReal (17408*cappedRepresentative nt) := ENNReal.tsum_le_tsum hreceiver
    _=ENNReal.ofReal 34816 := by
      convert capped_linear_radius_sum (by norm_num : (0:ℝ)≤17408) (by norm_num : (0:ℝ)≤1) using 1 <;> norm_num

end RVM

end

end OAI
