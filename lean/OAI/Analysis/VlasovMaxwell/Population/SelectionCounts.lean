import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.PartitionOccupation

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def representativeGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (φ/(p*θ^2)) *
    (∫⁻z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
        ∂physicalBinMeasure V B (Icc a b))

lemma Admissible.representative_good_Cauchy {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let B := representativeClosedBin T w k
      let O := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
          (max 0 (a-B.rmax)) (min T (b-B.rmin)))
      let E := datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
            (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_bin_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' _ _) le_rfl
        · rw [Real.volume_Icc]
          exact ENNReal.ofReal_le_ofReal hab
        · apply ENNReal.ofReal_le_ofReal
          rw [hBmax,hBmin]
          linarith only [hr]
      _ = _ := by rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)≤
      ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*datumEnergyNumber d)) := mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0<r/2; positivity) (by change 0<φ^2/2; positivity)
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  unfold representativeGoodCost
  dsimp only
  apply mul_le_mul' le_rfl
  apply hbnd.trans
  apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact min_le_min (mul_le_mul' le_rfl hmeasure) le_rfl

lemma direct_good_near_scalar {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*(H*h)*φ^2)))=
    (128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
  rw [sqrt_near_product (by positivity : 0≤20*I) (by norm_num : (0:ℝ)≤768)
    hI hE (mul_nonneg hH hh) hφ (by positivity)]
  rw [show (20:ℝ)*I*I=20*(I:ℝ)^2 from by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤20),Real.sqrt_sq hI,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤768),Real.sqrt_mul hH]
  have he : Real.sqrt (20:ℝ)*Real.sqrt 768=Real.sqrt 15360 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤20)]
    norm_num
  calc
    _ = (128*C*(Real.sqrt 20*Real.sqrt 768)*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
      field_simp
    _ = _ := by rw [he]

lemma direct_good_far_sqrt {C K E p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 0<H) (hh : 0<h) (hφ : 0<φ) :
    Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8)))=
      Real.sqrt (1024*C*K*E)*p*θ*Real.sqrt (p*O)/(H*h*φ) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤1024*C*K*E),
    Real.sq_sqrt (mul_nonneg hp.le hO)]
  field_simp
  ring

lemma direct_good_far_scalar {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8))))≤
      (Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [direct_good_far_sqrt hC hK hE hp hθ hO hH0 hh hφ]
  have hsq : Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E)=
      Real.sqrt (20480*C*K)*E*Real.sqrt I := by
    rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
    rw [show (20*I*E)*(1024*C*K*E)=((20480*C*K)*E^2)*I by ring,
      Real.sqrt_mul (by positivity : 0≤(20480*C*K)*E^2),
      Real.sqrt_mul (by positivity : 0≤20480*C*K),Real.sqrt_sq hE]
  calc
    _ = ((Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E))*Real.sqrt (p*O)/(θ*h))/H := by
      field_simp
    _ = ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)))/H := by
      rw [hsq]
      ring
    _ ≤ _ := div_le_self (by positivity) hH

lemma direct_good_near_ennreal {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ))=
    ENNReal.ofReal ((128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2)) := by
  rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*θ^2),
    ←ENNReal.ofReal_mul (sq_nonneg _),ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    direct_good_near_scalar hC hI hE hH hh hφ hp hθ]

lemma direct_good_far_ennreal {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))*(ENNReal.ofReal (K*O)*ENNReal.ofReal E/
        ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ))≤
    ENNReal.ofReal ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h))) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [←ENNReal.ofReal_mul (by positivity : 0≤K*O),
    ←ENNReal.ofReal_div_of_pos (by positivity : 0<(H*h)^2*φ^2/8),
    ←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (direct_good_far_scalar hC hK hE hI hp hθ hO hH hh hφ)

def selectionDecay : ℝ := (2:ℝ)^(-1/100000:ℝ)

lemma selectionDecay_pos : 0<selectionDecay := Real.rpow_pos_of_pos (by norm_num) _
lemma selectionDecay_lt_one : selectionDecay<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma selectionDecay_pow (n : ℕ) :
    selectionDecay^n=((2:ℝ)^n)^(-1/100000:ℝ) := by
  rw [selectionDecay,←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma cappedRepresentative_selection_pow (n : ℕ) :
    (cappedRepresentative n)^(1/100000:ℝ)=selectionDecay^n := by
  rw [selectionDecay_pow]
  dsimp [cappedRepresentative]
  rw [inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
  congr 1
  norm_num

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np≤cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma selectionWeight_gap_bound {P : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : sourceRepresentative N≤P) (h0 : k 0≤N) (h1 : k 1≤k 0+6) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤
      selectionDecay^(N-k 0)*selectionDecay^(k 0+6-k 1)*selectionDecay^(k 2)*selectionDecay^(k 3) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hN := sourceRepresentative_two_pow N
  have hle : k 1≤N+6 := by omega
  have hid : sourceRepresentative N*cappedRepresentative (k 1)=(2:ℝ)^(N+6-k 1) := by
    rw [hN]
    dsimp [cappedRepresentative]
    rw [inv_pow, pow_sub₀ (2:ℝ) (by norm_num) hle]
  have hdec : (P*cappedRepresentative (k 1))^(-1/100000:ℝ)≤ selectionDecay^(N+6-k 1) := by
    rw [selectionDecay_pow,←hid]
    exact Real.rpow_le_rpow_of_nonpos (by rw [hN]; positivity)
      (mul_le_mul_of_nonneg_right hP hθ.le) (by norm_num)
  have he : N+6-k 1=(N-k 0)+(k 0+6-k 1) := by omega
  unfold selectionWeight
  rw [cappedRepresentative_selection_pow,cappedRepresentative_selection_pow]
  rw [he,pow_add] at hdec
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdec
    (pow_nonneg selectionDecay_pos.le _)) (pow_nonneg selectionDecay_pos.le _)

lemma sum_selectionDecay (N : ℕ) :
    ∑n∈Finset.range N,selectionDecay^n≤(1-selectionDecay)⁻¹ := by
  have hr : |selectionDecay|<1 := by rw [abs_of_pos selectionDecay_pos]; exact selectionDecay_lt_one
  exact ((summable_geometric_of_abs_lt_one hr).sum_le_tsum (Finset.range N)
    (fun _ _=>pow_nonneg selectionDecay_pos.le _)).trans_eq (tsum_geometric_of_abs_lt_one hr)

lemma sum_selectionDecay_box (N : ℕ) :
    ∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  classical
  have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
      (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  have hh := Finset.sum_prod_piFinset (Finset.range N) (fun (_i : Fin 4) (n : ℕ)=>selectionDecay^n)
  rw [heq] at hh
  have hsum : (∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i))=
      (∑n∈Finset.range N,selectionDecay^n)^4 := by
    simpa [dyadicBox,Fin.prod_univ_four,pow_succ] using hh
  rw [hsum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))
    (sum_selectionDecay N) 4

lemma sum_selectionDecay_finset (S : Finset (Fin 4→ℕ)) :
    ∑k∈S,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  obtain ⟨N,hN⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _=>Finset.prod_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))).trans
    (sum_selectionDecay_box N)

lemma sum_selectionWeight (S : Finset (Fin 4→ℕ)) {P : ℝ}
    (hP : ∀k∈S,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈S,1/sourceRepresentative (k 0)≤cappedRepresentative (k 1)) :
    ∑k∈S,selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤((1-selectionDecay)⁻¹)^4 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.sup (fun k=>k 0)
    have hN (k) (hk : k∈S) : k 0≤N := Finset.le_sup (f:=fun k : Fin 4→ℕ=>k 0) hk
    have hNP : sourceRepresentative N≤P := by
      obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup S hS (fun k=>k 0)
      change sourceRepresentative (S.sup (fun k : Fin 4→ℕ=>k 0))≤P
      rw [he]
      exact hP k hk
    let g : (Fin 4→ℕ)→(Fin 4→ℕ) := fun k=>![N-k 0,k 0+6-k 1,k 2,k 3]
    have hg : Set.InjOn g ↑S := by
      intro k hk l hl hkl
      have hk1 := selection_angle_index (hθ k hk)
      have hl1 := selection_angle_index (hθ l hl)
      have h00 := congrFun hkl 0
      have h11 := congrFun hkl 1
      have h22 := congrFun hkl 2
      have h33 := congrFun hkl 3
      change N-k 0=N-l 0 at h00
      change k 0+6-k 1=l 0+6-l 1 at h11
      change k 2=l 2 at h22
      change k 3=l 3 at h33
      have hk0 := hN k hk
      have hl0 := hN l hl
      have h0e : k 0=l 0 := by omega
      have h1e : k 1=l 1 := by omega
      apply funext
      intro i
      fin_cases i
      · exact h0e
      · exact h1e
      · exact h22
      · exact h33
    calc
      _≤∑k∈S,∏i,selectionDecay^(g k i) := Finset.sum_le_sum (fun k hk=>by
        simpa [g,Fin.prod_univ_four] using selectionWeight_gap_bound hNP (hN k hk) (selection_angle_index (hθ k hk)))
      _=∑k∈S.image g,∏i,selectionDecay^(k i) := (Finset.sum_image (f:=fun k : Fin 4→ℕ=>∏i,selectionDecay^(k i)) (fun k hk l hl he=>hg hk hl he)).symm
      _≤_ := sum_selectionDecay_finset _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

lemma source_ratio_sq_le {p w : ℝ} (hp : 0<p) (_ : 0<w) :
    (p/min p w)^2≤1+(p/w)^2 := by
  rcases le_total p w with h|h
  · rw [min_eq_left h,div_self hp.ne',one_pow]
    linarith [sq_nonneg (p/w)]
  · rw [min_eq_right h]
    linarith

lemma source_ratio_sq_sum {P w : ℝ} (hP : 0≤P) (hw : 0<w) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤P) :
    ∑n∈S,(sourceRepresentative n/min (sourceRepresentative n) w)^2≤
      (S.card:ℝ)+2*(P/w)^2 := by
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  calc
    _≤∑n∈S,(1+(sourceRepresentative n/w)^2) :=
      Finset.sum_le_sum (fun n _=>source_ratio_sq_le (hp n) hw)
    _=(S.card:ℝ)+(∑n∈S,(sourceRepresentative n)^2)/w^2 := by
      simp_rw [Finset.sum_add_distrib,div_pow,←Finset.sum_div]
      simp
    _≤(S.card:ℝ)+(2*P^2)/w^2 := by
      gcongr
      calc
        _≤∑n∈S,P*sourceRepresentative n := Finset.sum_le_sum (fun n hn=>by
          nlinarith [mul_le_mul_of_nonneg_right (hS n hn) (hp n).le])
        _=P*(∑n∈S,sourceRepresentative n) := (Finset.mul_sum ..).symm
        _≤P*(2*P) := mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP S hS) hP
        _=2*P^2 := by ring
    _=_ := by ring

lemma pair_source_ratio_sq_sum {P w N : ℝ} (hP : 0≤P) (hw : 0<w)
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P)
    (hpN : ((S.image Prod.fst).card:ℝ)≤N) (hfN : ((S.image Prod.snd).card:ℝ)≤N) :
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2)≤
      N*(N+2*(P/w)^2) ∧
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2*cappedRepresentative n.2)≤
      2*(N+2*(P/w)^2) := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hN : 0≤N := (Nat.cast_nonneg U.card).trans hpN
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact hS k hk
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hu : (∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)≤N+2*(P/w)^2 :=
    (source_ratio_sq_sum hP hw U hU).trans (by gcongr)
  have hv : ∑n∈V,cappedRepresentative n≤2 := by
    have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) V (fun n _=>cappedRepresentative_le_one n)
    norm_num at hh
    exact hh
  constructor
  · calc
      _≤∑n∈U.product V,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
      _=(∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)*(V.card:ℝ) := by
        simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_const,nsmul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _≤(N+2*(P/w)^2)*N := mul_le_mul hu hfN (Nat.cast_nonneg _) (by positivity)
      _=_ := by ring
  · calc
      _≤∑n∈U.product V,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2*cappedRepresentative n.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>mul_nonneg (sq_nonneg _) (cappedRepresentative_pos _).le)
      _=(∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)*(∑n∈V,cappedRepresentative n) := by
        rw [Finset.product_eq_sprod,Finset.sum_product]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
      _≤(N+2*(P/w)^2)*2 := mul_le_mul hu hv (Finset.sum_nonneg (fun n _=>(cappedRepresentative_pos n).le)) (by positivity)
      _=_ := by ring

lemma joint_budget_Cauchy {E N x : ℝ} (hE : 0≤E) (hN : 0≤N) (hx : 0≤x)
    {ι : Type*} (S : Finset ι) (J W : ι→ℝ) (hJ : ∀i∈S,0≤J i)
    (hbudget : ∑i∈S,J i≤E) (hW : ∑i∈S,(W i)^2≤N*(N+2*x^2)) :
    ∑i∈S,W i*Real.sqrt (J i)≤Real.sqrt E*(N+2*Real.sqrt N*x) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S W (fun i=>Real.sqrt (J i))
  have he : (∑i∈S,(Real.sqrt (J i))^2)=∑i∈S,J i :=
    Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hJ i hi))
  rw [he] at hc
  have hu := mul_le_mul hW hbudget (Finset.sum_nonneg hJ) (by positivity : 0≤N*(N+2*x^2))
  have hs := Real.sq_sqrt hE
  have hn := Real.sq_sqrt hN
  have hb : 0≤Real.sqrt E*(N+2*Real.sqrt N*x) := by positivity
  have hsq : N*(N+2*x^2)*E≤(Real.sqrt E*(N+2*Real.sqrt N*x))^2 := by
    rw [mul_pow,hs]
    have he : (N+2*Real.sqrt N*x)^2=N^2+4*N*Real.sqrt N*x+4*N*x^2 := by
      ring_nf
      rw [hn]
      ring
    rw [he]
    nlinarith [mul_nonneg hE (mul_nonneg hN (mul_nonneg (Real.sqrt_nonneg N) hx)),
      mul_nonneg hE (mul_nonneg hN (sq_nonneg x))]
  exact le_of_sq_le_sq (hc.trans (hu.trans hsq)) hb

lemma joint_budget_weighted_Cauchy {E N x : ℝ} (hE : 0≤E) (hN : 0≤N) (hx : 0≤x)
    {ι : Type*} (S : Finset ι) (J W : ι→ℝ) (hJ : ∀i∈S,0≤J i)
    (hbudget : ∑i∈S,J i≤E) (hW : ∑i∈S,(W i)^2≤2*(N+2*x^2)) :
    ∑i∈S,W i*Real.sqrt (J i)≤Real.sqrt E*(2*Real.sqrt N+2*x) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S W (fun i=>Real.sqrt (J i))
  have he : (∑i∈S,(Real.sqrt (J i))^2)=∑i∈S,J i :=
    Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hJ i hi))
  rw [he] at hc
  have hu := mul_le_mul hW hbudget (Finset.sum_nonneg hJ) (by positivity : 0≤2*(N+2*x^2))
  have hs := Real.sq_sqrt hE
  have hn := Real.sq_sqrt hN
  have hb : 0≤Real.sqrt E*(2*Real.sqrt N+2*x) := by positivity
  have hsq : 2*(N+2*x^2)*E≤(Real.sqrt E*(2*Real.sqrt N+2*x))^2 := by
    rw [mul_pow,hs]
    have he : (2*Real.sqrt N+2*x)^2=4*N+8*Real.sqrt N*x+4*x^2 := by
      ring_nf
      rw [hn]
      ring
    rw [he]
    nlinarith [mul_nonneg hE (mul_nonneg (Real.sqrt_nonneg N) hx),mul_nonneg hE hN]
  exact le_of_sq_le_sq (hc.trans (hu.trans hsq)) hb

lemma shared_weighted_pair_Cauchy {P w N E : ℝ} (hP : 0≤P) (hw : 0<w) (hE : 0≤E)
    (S : Finset (ℕ×ℕ)) (J : ℕ×ℕ→ℝ) (hJ : ∀n∈S,0≤J n)
    (hbudget : ∑n∈S,J n≤E) (hS : ∀n∈S,sourceRepresentative n.1≤P)
    (hpN : ((S.image Prod.fst).card:ℝ)≤N) (hfN : ((S.image Prod.snd).card:ℝ)≤N) :
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))≤
      Real.sqrt E*(N+2*Real.sqrt N*(P/w)) ∧
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*
      Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))≤
      Real.sqrt E*(2*Real.sqrt N+2*(P/w)) := by
  have hN : 0≤N := (Nat.cast_nonneg _).trans hpN
  obtain ⟨h1,h2⟩ := pair_source_ratio_sq_sum hP hw S hS hpN hfN
  constructor
  · exact joint_budget_Cauchy hE hN (div_nonneg hP hw.le) S J _ hJ hbudget h1
  · apply joint_budget_weighted_Cauchy hE hN (div_nonneg hP hw.le) S J
      (fun n=>(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)) hJ hbudget
    simpa only [mul_pow,Real.sq_sqrt (cappedRepresentative_pos _).le] using h2

def pairCountConstant : ℝ := 2+1/Real.log 2
lemma pairCountConstant_pos : 0<pairCountConstant := by
  have h : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold pairCountConstant
  positivity

lemma exists_small_pair_count {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P)) :
    ∃N : ℕ, (N:ℝ)≤pairCountConstant*Real.log (2+P) ∧
    ∀np nf : ℕ,sourceRepresentative np≤P →
      1/sourceRepresentative np≤cappedRepresentative nf → np<N ∧ nf<N := by
  obtain ⟨N,hN,hcard⟩ := exists_dyadic_count_log hP
  refine ⟨N,?_,?_⟩
  · have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    apply hcard.trans
    have hl : Real.log P≤Real.log (2+P) := Real.log_le_log (zero_lt_one.trans_le hP) (by linarith)
    have hd := div_le_div_of_nonneg_right hl h2.le
    unfold pairCountConstant
    simp only [div_eq_mul_inv,one_mul] at hd ⊢
    nlinarith
  · intro np nf hp hf
    have hn : np+6<N := index_lt_of_two_pow_le (by rwa [←sourceRepresentative_two_pow]) hN
    have hnf := selection_angle_index hf
    omega

lemma small_pair_cardinals {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2) :
    ((S.image Prod.fst).card:ℝ)≤pairCountConstant*Real.log (2+P) ∧
    ((S.image Prod.snd).card:ℝ)≤pairCountConstant*Real.log (2+P) := by
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  have hp : S.image Prod.fst⊆Finset.range N := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hidx k.1 k.2 (hS k hk).1 (hS k hk).2).1
  have hf : S.image Prod.snd⊆Finset.range N := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hidx k.1 k.2 (hS k hk).1 (hS k hk).2).2
  constructor
  · have hc : ((S.image Prod.fst).card:ℝ)≤(N:ℝ) := by exact_mod_cast (Finset.card_le_card hp).trans_eq (Finset.card_range N)
    exact hc.trans hN
  · have hc : ((S.image Prod.snd).card:ℝ)≤(N:ℝ) := by exact_mod_cast (Finset.card_le_card hf).trans_eq (Finset.card_range N)
    exact hc.trans hN

lemma angle_sqrt_factor {A L φ : ℝ} (hA : 0≤A) (hL : 0≤L) (hφ : 0<φ) :
    φ*Real.sqrt (A*L/φ)=Real.sqrt (A*L)*Real.sqrt φ := by
  calc
    _=Real.sqrt (φ^2)*Real.sqrt (A*L/φ) := by rw [Real.sqrt_sq hφ.le]
    _=Real.sqrt (A*L*φ) := by
      rw [←Real.sqrt_mul (sq_nonneg φ)]
      congr 1
      field_simp
    _=_ := Real.sqrt_mul (mul_nonneg hA hL) φ

lemma shared_radius_expansion {P M A I p w φ J : ℝ}
    (hP : 0<P) (hM : 0≤M) (hA : 0≤A) (hI : 0≤I)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) :
    Real.sqrt I*(1+Real.sqrt (I/stabilityLength P 16384 M A p w φ)*Real.sqrt J)*p*φ=
      Real.sqrt I*p*φ+16384*I*P*(M*(p/min p w)*Real.sqrt J+
        Real.sqrt (A*Real.log (2+P))*(p/min p w)*Real.sqrt φ*Real.sqrt J) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : min p w≠0 := (lt_min hp hw).ne'
  have hf := angle_sqrt_factor hA hL hφ
  rw [sqrt_div_stabilityLength hP.le (by norm_num) hM hp.le hw.le hφ.le hI]
  unfold stabilityRate
  calc
    _=Real.sqrt I*p*φ+16384*(Real.sqrt I)^2*P*
        (M*(p/min p w)+(φ*Real.sqrt (A*Real.log (2+P)/φ))*(p/min p w))*Real.sqrt J := by
      field_simp
    _=_ := by rw [Real.sq_sqrt hI,hf]; ring

lemma source_receiver_pair_sum {P : ℝ} (hP : 0≤P) (S : Finset (ℕ×ℕ))
    (hS : ∀n∈S,sourceRepresentative n.1≤P) :
    ∑n∈S,sourceRepresentative n.1*cappedRepresentative n.2≤4*P := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact hS k hk
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hv : ∑n∈V,cappedRepresentative n≤2 := by
    have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) V (fun n _=>cappedRepresentative_le_one n)
    norm_num at hh
    exact hh
  calc
    _≤∑n∈U.product V,sourceRepresentative n.1*cappedRepresentative n.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _=>by
        have hp : 0<sourceRepresentative n.1 := by dsimp [sourceRepresentative]; positivity
        exact mul_nonneg hp.le (cappedRepresentative_pos _).le)
    _=(∑n∈U,sourceRepresentative n)*(∑n∈V,cappedRepresentative n) := by
      rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _≤(2*P)*2 := mul_le_mul (sourceRepresentative_sum_bound hP U hU) hv
      (Finset.sum_nonneg (fun n _=>(cappedRepresentative_pos _).le)) (by positivity)
    _=_ := by ring

lemma paired_count_Cauchy_factors {C L X : ℝ} (hC : 0≤C) (hL : 1≤L) (hX : 1≤X) :
    C*L+2*Real.sqrt (C*L)*X≤(C+2*Real.sqrt C)*L*X ∧
    2*Real.sqrt (C*L)+2*X≤(2*Real.sqrt C+2)*Real.sqrt L*X := by
  have hL0 : 0≤L := zero_le_one.trans hL
  have hX0 : 0≤X := zero_le_one.trans hX
  have hroot : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hrL : Real.sqrt L≤L := by nlinarith [Real.sq_sqrt hL0]
  rw [Real.sqrt_mul hC]
  constructor
  · have h1 : C*L≤C*L*X := le_mul_of_one_le_right (mul_nonneg hC hL0) hX
    have h2 : 2*(Real.sqrt C*Real.sqrt L)*X≤2*(Real.sqrt C*L)*X := by gcongr
    nlinarith
  · have h1 : 2*(Real.sqrt C*Real.sqrt L)≤2*(Real.sqrt C*Real.sqrt L)*X :=
      le_mul_of_one_le_right (by positivity) hX
    have h2 : 2*X≤2*Real.sqrt L*X := by nlinarith
    nlinarith

lemma shared_radius_pair_sum {P M A I w E : ℝ}
    (hP : 1≤P) (hL : 1≤Real.log (2+P)) (hM : 0≤M) (hA : 0≤A)
    (hI : 0≤I) (hw : 0<w) (hwP : w≤P) (hE : 0≤E)
    (S : Finset (ℕ×ℕ)) (J : ℕ×ℕ→ℝ) (hJ : ∀n∈S,0≤J n)
    (hbudget : ∑n∈S,J n≤E) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2) :
    let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
    (∑n∈S, Real.sqrt I*(1+Real.sqrt (I/stabilityLength P 16384 M A
      (sourceRepresentative n.1) w (cappedRepresentative n.2))*Real.sqrt (J n))*
      sourceRepresentative n.1*cappedRepresentative n.2)≤
      (4+16384*Real.sqrt E*D)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) := by
  dsimp only
  let L := Real.log (2+P)
  let C := pairCountConstant
  let D := C+4*Real.sqrt C+2
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤L := zero_le_one.trans hL
  have hC : 0≤C := pairCountConstant_pos.le
  have hD : 0≤D := by dsimp [D]; positivity
  have hS' : ∀n∈S,sourceRepresentative n.1≤P := fun n hn=>(hS n hn).1
  obtain ⟨hc1,hc2⟩ := small_pair_cardinals hP hL S hS
  obtain ⟨hb1,hb2⟩ := shared_weighted_pair_Cauchy hP0.le hw hE S J hJ hbudget hS' hc1 hc2
  obtain ⟨hf1,hf2⟩ := paired_count_Cauchy_factors hC hL ((one_le_div hw).mpr hwP)
  have hD1 : C+2*Real.sqrt C≤D := by dsimp [D]; linarith [Real.sqrt_nonneg C]
  have hD2 : 2*Real.sqrt C+2≤D := by dsimp [D]; linarith [Real.sqrt_nonneg C]
  have hu : (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))≤
      Real.sqrt E*(D*L*(P/w)) := by
    apply hb1.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg E)
    exact hf1.trans (by gcongr)
  have hv : (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))≤
      Real.sqrt E*(D*Real.sqrt L*(P/w)) := by
    apply hb2.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg E)
    exact hf2.trans (by gcongr)
  have hsum := source_receiver_pair_sum hP0.le S hS'
  have hex (n : ℕ×ℕ) (hn : n∈S) := shared_radius_expansion (J:=J n) hP0 hM hA hI
    (show 0<sourceRepresentative n.1 by dsimp [sourceRepresentative]; positivity) hw (cappedRepresentative_pos n.2)
  calc
    _=Real.sqrt I*(∑n∈S,sourceRepresentative n.1*cappedRepresentative n.2)+
        16384*I*P*(M*(∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))+
        Real.sqrt (A*L)*(∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))) := by
      rw [Finset.sum_congr rfl hex]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      · rw [←Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [L]
        ring
    _≤Real.sqrt I*(4*P)+16384*I*P*(M*(Real.sqrt E*(D*L*(P/w)))+
        Real.sqrt (A*L)*(Real.sqrt E*(D*Real.sqrt L*(P/w)))) := by gcongr
    _=4*(P*Real.sqrt I)+(16384*Real.sqrt E*D)*((M+Real.sqrt A)*I*P^2*L/w) := by
      rw [Real.sqrt_mul hA]
      have hr : (Real.sqrt L)^2=L := Real.sq_sqrt hL0
      simp only [div_eq_mul_inv]
      ring_nf
      rw [hr]
      ring
    _≤_ := by
      have hx : 0≤P*Real.sqrt I := by positivity
      have hy : 0≤(M+Real.sqrt A)*I*P^2*L/w := by positivity
      nlinarith [mul_nonneg (show 0≤16384*Real.sqrt E*D by positivity) hx]

lemma Admissible.representative_good_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
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
      representativeGoodCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P 512 16384 M A p w φ h I)/(θ*h))) := by
  obtain ⟨Cg,hCg,hcauchy⟩ := hd.representative_good_Cauchy
  let E := datumEnergyNumber d
  let H₀ := max 1 T₀
  let K := 1000000000*H₀^2
  let Cn := 128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H₀
  let Cf := Real.sqrt (20480*Cg*K)*E
  let C := max Cn Cf
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hK : 0≤K := by dsimp [K]; positivity
  have hCn : 0≤Cn := by dsimp [Cn]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hC : 0≤C := hCn.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
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
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
      (max 0 (a-B.rmax)) (min T (b-B.rmin)))
  let U := pureOccupationEnvelope P 512 16384 M A p w φ h I
  let D := ENNReal.ofReal (128*Cg*p^3*θ^2)
  let N := I*Real.sqrt h*p^2*φ^2
  let R := Real.sqrt I*Real.sqrt (p*U)/(θ*h)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH
  have hHH : H≤H₀ := max_le_max le_rfl hTT
  have hU : 0≤U := pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI.le
  have hN : 0≤N := by dsimp [N]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hc := hcauchy s T F hs hT zX k a b I w ha hb hI hJI
  change representativeGoodCost s F zX w k a b≤
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
        (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) at hc
  have ho : O≤ENNReal.ofReal (K*U)*ENNReal.ofReal E :=
    hoccup s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)))
      _ = ENNReal.ofReal ((128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*N) :=
        direct_good_near_ennreal hCg hI.le hE hH0 hh.le hφ.le hp hθ
      _ ≤ ENNReal.ofReal (C*N) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hN
        apply le_trans _ (le_max_left _ _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHH) (by positivity)
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D*(ENNReal.ofReal (K*U)*ENNReal.ofReal E/ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ)) := by
        apply mul_le_mul' le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact (min_le_right _ _).trans (mul_le_mul' le_rfl (ENNReal.div_le_div_right ho _))
      _ ≤ ENNReal.ofReal (Cf*R) := direct_good_far_ennreal hCg hK hE hI.le hp hθ hU hH hh hφ
      _ ≤ ENNReal.ofReal (C*R) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

def representativeSelected (P M A w I : ℝ) (k : Fin 4→ℕ) : Prop :=
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  P*Real.sqrt I*selectionWeight P θ φ h <
    min (I*Real.sqrt h*p^2*φ^2)
      (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P 512 16384 M A p w φ h I)/(θ*h))

def representativeSmallSector (P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤P ∧
    1/sourceRepresentative (k 0)≤cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}

lemma selectionWeight_nonneg {P θ φ h : ℝ} (hP : 0≤P) (hθ : 0≤θ) (hφ : 0≤φ) (hh : 0≤h) :
    0 ≤ selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selection_weighted_tsum {P c : ℝ} (hP0 : 0≤P) (hc : 0≤c)
    (Q : Set (Fin 4→ℕ)) (hP : ∀k∈Q,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈Q,1/sourceRepresentative (k 0)≤cappedRepresentative (k 1))
    (f : (Fin 4→ℕ)→ℝ≥0∞)
    (hf : ∀k∈Q,f k≤ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) :
    (∑'k,Q.indicator f k)≤ENNReal.ofReal (c*((1-selectionDecay)⁻¹)^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun k=>k∈Q)
  have hU (k) (hk : k∈U) : k∈Q := (Finset.mem_filter.mp hk).2
  have hsum : (∑k∈S,Q.indicator f k)=∑k∈U,f k := by simp [U,Finset.sum_filter,indicator_apply]
  rw [hsum]
  calc
    _ ≤ ∑k∈U,ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := Finset.sum_le_sum (fun k hk=>hf k (hU k hk))
    _ = ENNReal.ofReal (c*(∑k∈U,selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun k _=>mul_nonneg hc
        (selectionWeight_nonneg hP0 (cappedRepresentative_pos _).le
          (cappedRepresentative_pos _).le (cappedRepresentative_pos _).le)),Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_selectionWeight U (fun k hk=>hP k (hU k hk)) (fun k hk=>hθ k (hU k hk))) hc)

lemma Admissible.unselected_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*P*Real.sqrt I) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_good_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hbound M A hM hA,eventually_ge_atTop (1:ℝ)] with P hbnd hP
  intro s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hsource HZ
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  have hh := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*P*Real.sqrt I)
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>representativeGoodCost s F zX w k a b) (fun k hk=>by
      have he := hbnd s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hk.1.2.2 hsource HZ
      have hnot := le_of_not_gt hk.2
      exact he.trans (ENNReal.ofReal_le_ofReal (by
        have hmul := mul_le_mul_of_nonneg_left hnot hC
        simpa only [mul_assoc] using hmul)))
  convert hh using 1
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma small_power_four {x y e : ℝ} (hx : 0≤x) (hy : 0≤y)
    (he : 0≤e) (he1 : e≤1) (hxy : x≤4*y) : x^e≤4*y^e := by
  calc
    x^e≤(4*y)^e := Real.rpow_le_rpow hx hxy he
    _=(4:ℝ)^e*y^e := Real.mul_rpow (by norm_num) hy
    _≤4*y^e := mul_le_mul_of_nonneg_right (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) he1)
      (Real.rpow_nonneg hy _)

lemma small_negative_power_four {x y e : ℝ} (hx : 0<x) (hy : 0<y)
    (he : 0≤e) (he1 : e≤1) (hyx : y≤4*x) : x^(-e)≤4*y^(-e) := by
  have hinv : x⁻¹≤4*y⁻¹ := by
    rw [inv_eq_one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hx hy).mpr (by simpa using hyx)
  simpa only [Real.rpow_neg_eq_inv_rpow] using small_power_four (inv_nonneg.mpr hx.le)
    (inv_nonneg.mpr hy.le) he he1 hinv

lemma selectionWeight_neighbor {P : ℝ} (hP : 0<P) {j k : Fin 4→ℕ}
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤64*
    selectionWeight P (cappedRepresentative (j 1)) (cappedRepresentative (j 2))
      (cappedRepresentative (j 3)) := by
  have hc (n : ℕ) : 0<cappedRepresentative n := cappedRepresentative_pos _
  have hθ := small_negative_power_four (mul_pos hP (hc (k 1))) (mul_pos hP (hc (j 1)))
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (show P*cappedRepresentative (j 1)≤4*(P*cappedRepresentative (k 1)) from by
      have hh := mul_le_mul_of_nonneg_left (cappedRepresentative_le_four (hjk 1).2) hP.le
      simpa only [mul_left_comm] using hh)
  have hφ := small_power_four (hc (k 2)).le (hc (j 2)).le
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (cappedRepresentative_le_four (hjk 2).1)
  have hh := small_power_four (hc (k 3)).le (hc (j 3)).le
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (cappedRepresentative_le_four (hjk 3).1)
  have hjθ := hc (j 1)
  have hjφ := hc (j 2)
  have hjh := hc (j 3)
  have hkθ := hc (k 1)
  have hkφ := hc (k 2)
  have hkh := hc (k 3)
  unfold selectionWeight
  simp only [neg_div]
  calc
    _≤(4*(P*cappedRepresentative (j 1))^(-(1/100000:ℝ)))*
        (4*(cappedRepresentative (j 2))^(1/100000:ℝ))*
        (4*(cappedRepresentative (j 3))^(1/100000:ℝ)) := by
      apply mul_le_mul (mul_le_mul hθ hφ (by positivity) (by positivity)) hh (by positivity) (by positivity)
    _=_ := by ring

lemma selected_neighbor_near_lower {P M A w I : ℝ} (hP : 0<P) (hI : 0<I)
    {j k : Fin 4→ℕ} (hj : representativeSelected P M A w I j)
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    P*Real.sqrt I*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) <
      32768*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
        (cappedRepresentative (k 2))^2) := by
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hc (n : ℕ) : 0<cappedRepresentative n := cappedRepresentative_pos _
  have hnear := lt_of_lt_of_le hj (min_le_left _ _)
  have hsqrt : Real.sqrt (cappedRepresentative (j 3))≤2*Real.sqrt (cappedRepresentative (k 3)) := by
    calc
      _≤Real.sqrt (4*cappedRepresentative (k 3)) := Real.sqrt_le_sqrt (cappedRepresentative_le_four (hjk 3).2)
      _=_ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hcost : I*Real.sqrt (cappedRepresentative (j 3))*(sourceRepresentative (j 0))^2*
      (cappedRepresentative (j 2))^2≤512*(I*Real.sqrt (cappedRepresentative (k 3))*
        (sourceRepresentative (k 0))^2*(cappedRepresentative (k 2))^2) := by
    calc
      _≤I*(2*Real.sqrt (cappedRepresentative (k 3)))*(4*sourceRepresentative (k 0))^2*
          (4*cappedRepresentative (k 2))^2 := by
        apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hI.le)
          (pow_le_pow_left₀ (hp _).le (sourceRepresentative_le_four (hjk 0).1) 2) (by positivity) (by positivity))
          (pow_le_pow_left₀ (hc _).le (cappedRepresentative_le_four (hjk 2).2) 2) (by positivity) (by positivity)
      _=_ := by ring
  calc
    _≤64*(P*Real.sqrt I*selectionWeight P (cappedRepresentative (j 1))
        (cappedRepresentative (j 2)) (cappedRepresentative (j 3))) := by
      have hh := mul_le_mul_of_nonneg_left (selectionWeight_neighbor hP hjk)
        (mul_nonneg hP.le (Real.sqrt_nonneg I))
      simpa only [mul_left_comm] using hh
    _<64*(I*Real.sqrt (cappedRepresentative (j 3))*(sourceRepresentative (j 0))^2*
        (cappedRepresentative (j 2))^2) := mul_lt_mul_of_pos_left hnear (by norm_num)
    _≤64*(512*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
        (cappedRepresentative (k 2))^2)) := mul_le_mul_of_nonneg_left hcost (by norm_num)
    _=_ := by ring

end RVM

end

end OAI
