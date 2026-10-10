import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ObservationCone
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalElectricKernel
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixClamp

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma retarded_same_time_separation {X a : ℝ → Vec} {s t C : ℝ} {y n : Vec}
    (hst : s≤t)
    (hX : ∀ r ∈ Icc s t, HasDerivWithinAt X (a r) (Icc s t) r)
    (hvel : ∀ r ∈ Icc s t, ‖a r-n‖≤C)
    (hgeom : X t-y=(t-s) • n) : ‖y-X s‖≤C*(t-s) := by
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivWithinAt (fun r => X r-r • n) (a r-n) (Icc s t) r := by
    have hn : HasDerivWithinAt (fun r : ℝ => r • n) n (Icc s t) r := by
      convert ((hasDerivAt_id r).smul_const n).hasDerivWithinAt using 1 <;> try rfl
      exact (one_smul ℝ n).symm
    exact (hX r hr).sub hn
  have hh := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hvel (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  have hid : X t-t • n-(X s-s • n)=y-X s := by
    have he : X t=y+(t-s) • n := by rw [← hgeom]; abel
    rw [he,sub_smul]
    module
  simpa only [hid,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh

lemma velocity_ref_triangle {v a A n : Vec} {η φ : ℝ}
    (hv : ‖v-A‖≤η) (ha : ‖a-A‖≤η) (han : ‖a-n‖≤φ) :
    ‖v-n‖≤φ+2*η := by
  have he : v-n=(v-A)-(a-A)+(a-n) := by abel
  rw [he]
  have hh := (norm_add_le ((v-A)-(a-A)) (a-n)).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hv ha)) han)
  linarith

lemma relative_ref_triangle {u a U A : Vec} {η : ℝ}
    (hu : ‖u-U‖≤η) (ha : ‖a-A‖≤η) : ‖u-a-(U-A)‖≤2*η := by
  have he : u-a-(U-A)=(u-U)-(a-A) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

lemma PhaseFlowOn.retarded_stable_cell_occupation
    {s : Solution} {T M A P L a b t₀ p c φ h : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (ha : 0≤a) (hb : b≤T) (ht₀ : t₀ ∈ Icc a b)
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L)
    (hc : 0<c) (hc1 : c≤1) (hcφ : c≤φ) (_hh : 0≤h)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    {H : Phase → Set ℝ} (hHC : ∀ z, H z ⊆ Icc a b)
    (hret : ∀ z r, r ∈ H z → ∃ t ∈ Icc r b, ∃ n : Vec,
      t-r≤h ∧ (F.flow zX t).1-(F.flow z r).1=(t-r) • n ∧
        ‖velocity (F.flow zX t).2-n‖≤φ)
    (href : ∀ z, (H z).Nonempty →
      IncrementBootstrap (fun t => (F.flow z t).2) T M A P L ∧
      ∃ r ∈ Icc a b, ∃ t ∈ Icc a b,
        p≤q (F.flow z r).2 ∧
        c≤‖velocity (F.flow z r).2-velocity (F.flow zX t).2‖ ∧
        M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (F.flow z r).2 ≤
          c*q (F.flow z r).2/16 ∧
        M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (F.flow zX t).2 ≤
          c*q (F.flow zX t).2/16) :
    ENNReal.ofReal (p/2) * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal (8*h*φ/c) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hCT : Icc a b ⊆ Icc (0:ℝ) T := Icc_subset_Icc ha hb
  have hmem (z : Phase) :
      ContinuousOn (fun t => (F.flow z t).2) (Icc a b) :=
    (F.continuousOn_time z).snd.mono hCT
  have hstable (z : Phase) (HZ : IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
      (r : ℝ) (hr : r ∈ Icc a b)
      (hst : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (F.flow z r).2 ≤
        c*q (F.flow z r).2/16) :
      ∀ t ∈ Icc a b, ‖velocity (F.flow z t).2-velocity (F.flow z r).2‖≤c/8 ∧
        q (F.flow z r).2/2≤q (F.flow z t).2 := by
    have hq := q_pos (F.flow z r).2
    have hε : c*q (F.flow z r).2/16<q (F.flow z r).2/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc1 hq.le]
    have he : 2*(c*q (F.flow z r).2/16)/q (F.flow z r).2=c/8 := by field_simp; ring
    intro t ht
    have hh := HZ.velocity_stopped_about ha hb hr (hmem z) hM hA hP hL hε hst t ht
    exact ⟨by simpa only [he] using hh.2.1,hh.2.2.1⟩
  have hdata (z : Phase) (hz : (H z).Nonempty) :
      volume (H z)≤ENNReal.ofReal (8*h*φ/c) ∧ p/2≤q (F.flow z t₀).2 := by
    obtain ⟨HZ,r,hr,t,ht,hp,hsep,hst,hstX⟩ := href z hz
    have hZ := hstable z HZ r hr hst
    have hX := hstable zX HX t ht hstX
    refine ⟨?_,(by linarith [(hZ t₀ ht₀).2])⟩
    have hseparation (u : ℝ) (hu : u ∈ H z) :
        ‖(F.flow z u).1-(F.flow zX u).1‖≤2*h*φ := by
      have huC := hHC z hu
      obtain ⟨v,hv,n,hvh,hgeom,hangle⟩ := hret z u hu
      have hvC : v ∈ Icc a b := ⟨huC.1.trans hv.1,hv.2⟩
      have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc huC.1 hvC.2
      have hbnd := retarded_same_time_separation hv.1
        (fun w hw => ((F.ode zX w (hCT (hsub hw))).mono
          (hsub.trans hCT)).fst)
        (fun w hw => velocity_ref_triangle (hX w (hsub hw)).1 (hX v hvC).1 hangle)
        hgeom
      have hφ : 0≤φ := hc.le.trans hcφ
      calc
        _ ≤ (φ+2*(c/8))*(v-u) := hbnd
        _ ≤ (2*φ)*h := mul_le_mul (by linarith) hvh (sub_nonneg.mpr hv.1) (by positivity)
        _ = 2*h*φ := by ring
    have hvel (u : ℝ) (hu : u ∈ interior (Icc a b)) :
        ‖velocity (F.flow z u).2-velocity (F.flow zX u).2-
          (velocity (F.flow z r).2-velocity (F.flow zX t).2)‖≤c/2 := by
      exact (relative_ref_triangle (hZ u (interior_subset hu)).1
        (hX u (interior_subset hu)).1).trans (by linarith)
    have hdur := stable_cell_duration (convex_Icc a b) (hHC z) hc hsep
      ((F.continuousOn_time zX).fst.mono hCT)
      ((F.continuousOn_time z).fst.mono hCT)
      (fun u hu => (F.ode zX u (hCT (interior_subset hu))).hasDerivAt
        (Icc_mem_nhds (by rw [interior_Icc] at hu; linarith [hu.1])
          (by rw [interior_Icc] at hu; linarith [hu.2])) |>.fst)
      (fun u hu => (F.ode z u (hCT (interior_subset hu))).hasDerivAt
        (Icc_mem_nhds (by rw [interior_Icc] at hu; linarith [hu.1])
          (by rw [interior_Icc] at hu; linarith [hu.2])) |>.fst)
      hvel hseparation
    convert hdur using 1
    congr 1
    ring
  apply F.label_occupation_cell_bound hs (hCT ht₀) _ (fun z hz => (hdata z hz).2)
  intro z
  by_cases hz : (H z).Nonempty
  · exact (hdata z hz).1
  · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]

lemma exists_axis_basis (a : Vec) : ∃ b : OrthonormalBasis (Fin 3) ℝ Vec,
    ∀ i, i≠0 → dot (b i) a=0 := by
  classical
  by_cases ha : a=0
  · exact ⟨EuclideanSpace.basisFun (Fin 3) ℝ,fun i _ => by simp [ha,dot]⟩
  have hpos : 0<‖a‖ := norm_pos_iff.mpr ha
  let n : Vec := ‖a‖⁻¹ • a
  have hn : ‖n‖=1 := by simp [n,norm_smul,hpos.ne']
  have horth : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => n)) := by
    rw [orthonormal_subsingleton_iff]
    exact fun _ => hn
  obtain ⟨b,hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ Vec=Fintype.card (Fin 3) by simp)
  refine ⟨b,fun i hi => ?_⟩
  have hzero := b.orthonormal.inner_eq_zero hi
  rw [hb 0 (mem_singleton _)] at hzero
  have he : a=‖a‖ • n := by simp [n,smul_smul,hpos.ne']
  rw [dot_eq_inner,he,inner_smul_right,hzero,mul_zero]

lemma volume_axis_box (b : OrthonormalBasis (Fin 3) ℝ Vec) {R S : ℝ}
    (hR : 0≤R) (hS : 0≤S) :
    volume {v : Vec | |dot (b 0) v|≤R ∧ |dot (b 1) v|≤S ∧ |dot (b 2) v|≤S} =
      ENNReal.ofReal (8*R*S^2) := by
  let F : Vec → Fin 3 → ℝ := fun v => WithLp.ofLp (b.repr v)
  have hp : MeasurePreserving F volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr
  let A : Set (Fin 3 → ℝ) := Icc ![-R,-S,-S] ![R,S,S]
  have he : {v : Vec | |dot (b 0) v|≤R ∧ |dot (b 1) v|≤S ∧ |dot (b 2) v|≤S}=F ⁻¹' A := by
    ext v
    simp only [mem_ofPred_eq,mem_preimage,A,mem_Icc,Pi.le_def,F,OrthonormalBasis.repr_apply_apply,
      ← dot_eq_inner,Fin.forall_fin_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.forall_fin_zero,and_true]
    simp only [abs_le]
    tauto
  rw [he,hp.measure_preimage measurableSet_Icc.nullMeasurableSet,Real.volume_Icc_pi]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_succ,Fin.prod_univ_zero,
    mul_one,sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma volume_velocity_cap {P δ : ℝ} (hP : 0≤P) (hδ : 0≤δ) (a : Vec) :
    volume {v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ} ≤ ENNReal.ofReal (8*P^3*δ^2) := by
  obtain ⟨b,hb⟩ := exists_axis_basis a
  have hsub : {v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ} ⊆
      {v : Vec | |dot (b 0) v|≤P ∧ |dot (b 1) v|≤P*δ ∧ |dot (b 2) v|≤P*δ} := by
    intro v hv
    have hn : ‖v‖≤P := (norm_lt_q v).le.trans hv.1
    have hall (i : Fin 3) : |dot (b i) v|≤P := by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm _ _).trans (by simpa only [b.orthonormal.norm_eq_one,one_mul] using hn)
    have hsmall (i : Fin 3) (hi : i≠0) : |dot (b i) v|≤P*δ := by
      have hd : |dot (b i) (velocity v-a)|≤δ := by
        rw [dot_eq_inner]
        exact (abs_real_inner_le_norm _ _).trans (by simpa only [b.orthonormal.norm_eq_one,one_mul] using hv.2)
      rw [dot_sub_right,hb i hi,sub_zero,velocity,dot_smul_right,abs_mul,
        abs_of_pos (inv_pos.mpr (q_pos v))] at hd
      have hh := (mul_le_mul_of_nonneg_left hd (q_pos v).le)
      rw [← mul_assoc,mul_inv_cancel₀ (q_pos v).ne',one_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hv.1 hδ)
    exact ⟨hall 0,hsmall 1 (by decide),hsmall 2 (by decide)⟩
  have hh := (measure_mono hsub).trans_eq (volume_axis_box b hP (mul_nonneg hP hδ))
  convert hh using 1
  congr 1
  ring

lemma lintegral_velocity_cap_density {P δ C : ℝ} (hP : 0≤P) (hδ : 0≤δ)
    (hC : 0≤C) (a : Vec) {g : Vec → ℝ} (hg : ∀ v, g v≤C)
    {H : Set Vec} (hH : H⊆{v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ}) :
    (∫⁻ v in H, ENNReal.ofReal (g v))≤ENNReal.ofReal (8*C*P^3*δ^2) := by
  calc
    _ ≤ ∫⁻ _v in H, ENNReal.ofReal C := lintegral_mono (fun v => ENNReal.ofReal_le_ofReal (hg v))
    _ = ENNReal.ofReal C * volume H := by rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (8*P^3*δ^2) := by
      gcongr
      exact (measure_mono hH).trans (volume_velocity_cap hP hδ a)
    _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring

lemma sphere_cap_area {δ : ℝ} (hδ : 0≤δ) (a : Vec) :
    sphereMeasure {n : Sphere | ‖n.1-a‖≤δ}≤ENNReal.ofReal (24*δ^2) := by
  classical
  let A : Set Sphere := {n | ‖n.1-a‖≤δ}
  have hA : MeasurableSet A := isClosed_le
    ((continuous_subtype_val.sub continuous_const).norm) continuous_const |>.measurableSet
  obtain ⟨b,hb⟩ := exists_axis_basis a
  let B : Set Vec := {v | |dot (b 0) v|≤1 ∧ |dot (b 1) v|≤δ ∧ |dot (b 2) v|≤δ}
  have hsub : Set.image2 (fun (r : ℝ) (n : Vec) => r • n) (Ioo 0 1) (Subtype.val '' A)⊆B := by
    rintro v ⟨r,hr,n,⟨N,hN,rfl⟩,rfl⟩
    have hh (i : Fin 3) : |dot (b i) N.1|≤1 := by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm _ _).trans_eq (by rw [b.orthonormal.norm_eq_one,sphere_norm,one_mul])
    have ht (i : Fin 3) (hi : i≠0) : |dot (b i) N.1|≤δ := by
      have hd := abs_real_inner_le_norm (b i) (N.1-a)
      rw [← dot_eq_inner,dot_sub_right,hb i hi,sub_zero,b.orthonormal.norm_eq_one,one_mul] at hd
      exact hd.trans hN
    have hm (i : Fin 3) (D : ℝ) (hD : 0≤D) (hi : |dot (b i) N.1|≤D) :
        |dot (b i) (r • N.1)|≤D := by
      rw [dot_smul_right,abs_mul,abs_of_pos hr.1]
      exact (mul_le_mul_of_nonneg_left hi hr.1.le).trans (by nlinarith [hr.2])
    exact ⟨hm 0 1 zero_le_one (hh 0),hm 1 δ hδ (ht 1 (by decide)),hm 2 δ hδ (ht 2 (by decide))⟩
  rw [show {n : Sphere | ‖n.1-a‖≤δ}=A from rfl,(volume : Measure Vec).toSphere_apply' hA]
  have hdim : Module.finrank ℝ Vec=3 := by simp
  rw [hdim]
  change (3 : ENNReal) * volume (Set.image2 (fun (r : ℝ) (n : Vec) => r • n) (Ioo 0 1) (Subtype.val '' A))≤_
  calc
    _ ≤ 3*volume B := by gcongr
    _ = 3*ENNReal.ofReal (8*1*δ^2) := by rw [volume_axis_box b zero_le_one hδ]
    _ = _ := by rw [show (3:ENNReal)=ENNReal.ofReal 3 by norm_num,← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

lemma norm_sub_le_of_deficit {u a : Vec} {δ : ℝ} (hu : ‖u‖≤1) (ha : ‖a‖≤1)
    (hδ : 0≤δ) (hd : 1-dot u a≤δ^2/2) : ‖u-a‖≤δ := by
  have he : ‖u-a‖^2=‖u‖^2+‖a‖^2-2*dot u a := by rw [norm_sub_sq_real,dot_eq_inner]; ring
  have hu2 : ‖u‖^2≤1 := by nlinarith [norm_nonneg u]
  have ha2 : ‖a‖^2≤1 := by nlinarith [norm_nonneg a]
  nlinarith [norm_nonneg (u-a)]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) : Set Vec :=
  {v | q v ∈ Icc B.qmin B.qmax ∧ 1-dot n (velocity v) ∈ Icc B.dmin B.dmax ∧
    1-dot a (velocity v) ∈ Icc B.emin B.emax}

lemma measurableSet_coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) :
    MeasurableSet (coneBinMomentumSet B n a) := by
  exact ((measurableSet_Icc.preimage (contDiff_q (k:=0)).continuous.measurable).inter
    ((measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable).inter
      (measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable)))

lemma coneBinMomentumSet_subset_cap {B : ClosedConeBin} {n a : Vec} {P θ σ : ℝ}
    (hn : ‖n‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2) (he : B.emax ≤ 8*σ^2) :
    (coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-n‖ ≤ 4*θ}) ∧
    (coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-a‖ ≤ 4*σ}) := by
  have hcap (v b : Vec) (hb : ‖b‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
      (hv : 1-dot b (velocity v) ≤ 8*δ^2) : ‖velocity v-b‖ ≤ 4*δ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le hb (by positivity)
    rw [dot_comm]
    nlinarith
  constructor
  · intro v hv
    exact ⟨hv.1.2.trans hq,hcap v n hn θ hθ (hv.2.1.2.trans hd)⟩
  · intro v hv
    exact ⟨hv.1.2.trans hq,hcap v a ha σ hσ (hv.2.2.2.trans he)⟩

lemma coneBin_density_bound {B : ClosedConeBin} {n a : Vec} {P θ σ C : ℝ}
    (hn : ‖n‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2) (he : B.emax ≤ 8*σ^2)
    {g : Vec → ℝ} (hg : ∀ v, g v ≤ C) :
    (∫⁻ v in coneBinMomentumSet B n a, ENNReal.ofReal (g v))  ≤
      ENNReal.ofReal (128*C*P^3*(min θ σ)^2) := by
  have hh := coneBinMomentumSet_subset_cap hn ha hθ hσ hq hd he
  rcases le_total θ σ with h|h
  · rw [min_eq_left h]
    convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*θ) hC n hg hh.1 using 1
    congr 1
    ring
  · rw [min_eq_right h]
    convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*σ) hC a hg hh.2 using 1
    congr 1
    ring

lemma coneBin_density_small_bound {B : ClosedConeBin} {n a : Vec} {P θ C : ℝ}
    (hn : ‖n‖ ≤ 1) (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2)
    {g : Vec → ℝ} (hg : ∀ v, g v ≤ C) :
    (∫⁻ v in coneBinMomentumSet B n a, ENNReal.ofReal (g v))  ≤
      ENNReal.ofReal (128*C*P^3*θ^2) := by
  have hsub : coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-n‖ ≤ 4*θ} := by
    intro v hv
    refine ⟨hv.1.2.trans hq,?_⟩
    apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le hn (by positivity)
    rw [dot_comm]
    nlinarith [hv.2.1.2]
  convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*θ) hC n hg hsub using 1
  congr 1
  ring

lemma receiver_bin_area {B : ClosedConeBin} {a : Vec} {φ : ℝ}
    (ha : ‖a‖ ≤ 1) (hφ : 0 ≤ φ) (hD : B.Dmax ≤ 8*φ^2) :
    sphereMeasure {n : Sphere | 1-dot n.1 a ∈ Icc B.Dmin B.Dmax}  ≤
      ENNReal.ofReal (384*φ^2) := by
  have hsub : {n : Sphere | 1-dot n.1 a ∈ Icc B.Dmin B.Dmax}⊆
      {n : Sphere | ‖n.1-a‖ ≤ 4*φ} := by
    intro n hn
    apply norm_sub_le_of_deficit (sphere_norm n).le ha (by positivity)
    nlinarith [hn.2]
  convert (measure_mono hsub).trans (sphere_cap_area (by positivity : 0 ≤ 4*φ) a) using 1
  congr 1
  ring

lemma PhaseFlowOn.particle_uniform_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ z, 0 ≤ s.f (t,z) ∧ s.f (t,z) ≤ C := by
  have hc : Continuous (fun z => s.f (0,z)) := hs.f_smooth.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  obtain ⟨K,hK,hsub⟩ := hs.compact
  have hk : HasCompactSupport (fun z => s.f (0,z)) :=
    HasCompactSupport.intro hK (fun z hz => by
      by_contra hf
      exact hz (hsub 0 ⟨le_rfl,hT⟩ (subset_tsupport _ hf)))
  obtain ⟨C,hC⟩ := hc.bounded_above_of_compact_support hk
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro t ht z
  refine ⟨hs.nonnegative t ht z,?_⟩
  rw [F.transport_inverse hs.f_smooth hs.vlasov ht]
  exact (le_abs_self _).trans ((hC _).trans (le_max_right _ _))

def physicalBinDensity (s : Solution) (X V : ℝ → Vec) (B : ClosedConeBin)
    (t r : ℝ) (n : Sphere) : ℝ≥0∞ :=
  ∫⁻ v in coneBinMomentumSet B n.1 (velocity (V t)),
    ENNReal.ofReal (s.f (r,(X t-(t-r) • n.1,v)))

lemma PhaseFlowOn.physicalBinDensity_bounds {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X V : ℝ → Vec) (B : ClosedConeBin) (t r : ℝ) (n : Sphere)
        (P θ σ : ℝ), r ∈ Icc 0 T → 0 ≤ P → 0 ≤ θ → 0 ≤ σ →
        B.qmax ≤ P → B.dmax ≤ 8*θ^2 → B.emax ≤ 8*σ^2 →
      physicalBinDensity s X V B t r n  ≤  ENNReal.ofReal (128*C*P^3*(min θ σ)^2) := by
  obtain ⟨C,hC,hbound⟩ := F.particle_uniform_bound hs hT
  refine ⟨C,hC,?_⟩
  intro X V B t r n P θ σ hr hP hθ hσ hq hd he
  exact coneBin_density_bound (sphere_norm n).le (norm_velocity_lt_one _).le hP hθ hσ hC
    hq hd he (fun v => (hbound r hr _).2)

abbrev ConeCoordinate := ℝ × ℝ × Sphere

def physicalBinBase (V : ℝ → Vec) (B : ClosedConeBin) (J : Set ℝ) : Set ConeCoordinate :=
  {z | z.1 ∈ J ∧ z.2.1 ∈ Icc 0 z.1 ∧ z.1-z.2.1 ∈ Icc B.rmin B.rmax ∧
    q (V z.1) ∈ Icc B.wmin B.wmax ∧
    1-dot z.2.2.1 (velocity (V z.1)) ∈ Icc B.Dmin B.Dmax}

def physicalBinMeasure (V : ℝ → Vec) (B : ClosedConeBin) (J : Set ℝ) : Measure ConeCoordinate :=
  (volume.prod (volume.prod sphereMeasure)).restrict (physicalBinBase V B J)

lemma measurableSet_physicalBinBase {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinBase V B J) := by
  have htime : MeasurableSet {z : ConeCoordinate | z.2.1 ∈ Icc 0 z.1} :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
  exact (hJ.preimage measurable_fst).inter (htime.inter
    ((measurableSet_Icc.preimage (measurable_fst.sub (measurable_fst.comp measurable_snd))).inter
      ((measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp
        (hV.comp measurable_fst))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp
        ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
          ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))))))

lemma physicalBinMeasure_volume {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {φ : ℝ}
    (hφ : 0 ≤ φ) (hD : B.Dmax ≤ 8*φ^2) :
    physicalBinMeasure V B J univ ≤
      volume J * ENNReal.ofReal (B.rmax-B.rmin) * ENNReal.ofReal (384*φ^2) := by
  let A : Set ConeCoordinate := {z | z.1 ∈ J ∧
    z.2.1 ∈ Icc (z.1-B.rmax) (z.1-B.rmin) ∧
    ‖z.2.2.1-velocity (V z.1)‖ ≤ 4*φ}
  have hA : MeasurableSet A := by
    exact (hJ.preimage measurable_fst).inter
      (((measurableSet_le (measurable_fst.sub_const _) (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.sub_const _))).inter
      (measurableSet_le (((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).sub
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst))).norm) measurable_const))
  have hsub : physicalBinBase V B J ⊆ A := by
    intro z hz
    refine ⟨hz.1,⟨by linarith [hz.2.2.1.2],by linarith [hz.2.2.1.1]⟩,?_⟩
    apply norm_sub_le_of_deficit (sphere_norm z.2.2).le (norm_velocity_lt_one _).le (by positivity)
    nlinarith [hz.2.2.2.2.2]
  have hmass : (volume.prod (volume.prod sphereMeasure)) A = ∫⁻ t in J,
      ENNReal.ofReal (B.rmax-B.rmin) * sphereMeasure {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ} := by
    rw [← lintegral_indicator_one hA,lintegral_prod _ (measurable_one.indicator hA).aemeasurable]
    rw [← lintegral_indicator hJ]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]
      have he : (fun p : ℝ × Sphere => A.indicator (fun _ => (1:ℝ≥0∞)) (t,p)) =
          ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}).indicator (fun _ => 1) := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻ p : ℝ × Sphere, A.indicator (fun _ => (1:ℝ≥0∞)) (t,p) ∂(volume.prod sphereMeasure)) = _
      rw [he]
      have hS : MeasurableSet ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ
          {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}) :=
        measurableSet_Icc.prod (measurableSet_le
          ((continuous_subtype_val.sub continuous_const).norm.measurable) measurable_const)
      have hsi := lintegral_indicator_one (μ := volume.prod sphereMeasure) hS
      calc
        _ = (volume.prod sphereMeasure) ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ
            {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}) := hsi
        _ = _ := by
          rw [Measure.prod_prod,Real.volume_Icc]
          congr 2
          ring
    · rw [indicator_of_notMem ht]
      have he : (fun p : ℝ × Sphere => A.indicator (fun _ => (1:ℝ≥0∞)) (t,p))=0 := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻ p : ℝ × Sphere, A.indicator (fun _ => (1:ℝ≥0∞)) (t,p) ∂(volume.prod sphereMeasure)) = _
      rw [he]
      change (∫⁻ _ : ℝ × Sphere, (0:ℝ≥0∞) ∂(volume.prod sphereMeasure)) = 0
      exact lintegral_zero
  unfold physicalBinMeasure
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ (volume.prod (volume.prod sphereMeasure)) A := measure_mono hsub
    _ = _ := hmass
    _ ≤ ∫⁻ _t in J, ENNReal.ofReal (B.rmax-B.rmin) * ENNReal.ofReal (384*φ^2) := by
      apply lintegral_mono
      intro t
      apply mul_le_mul' le_rfl
      convert sphere_cap_area (by positivity : 0 ≤ 4*φ) (velocity (V t)) using 1
      congr 1
      ring
    _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]; ac_rfl

end RVM

end

end OAI
