import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CappedRepresentativePos

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_time_budget {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : 0<B.rmin) (hd : 0≤B.dmin) (hD : 0<B.Dmax) :
    ENNReal.ofReal (B.dmin/B.Dmax)*coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b c d)≤
      ENNReal.ofReal (b-a)*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  let H := closedBinEulerian F.flow zX T B S a b c d
  have hmem (z : Phase) (r : ℝ) (hh : (r,z)∈phaseHits F.flow T H) :
      branchTime F.flow zX z T r∈Icc a b ∧
      B.dmin≤1-dot (branchDirection F.flow zX z T r) (velocity (F.flow z r).2) ∧
      1-dot (branchDirection F.flow zX z T r)
        (velocity (F.flow zX (branchTime F.flow zX z T r)).2)≤B.Dmax := by
    have hb := ((F.mem_closedBinEulerian_iff zX z B S hC).mp hh.2).1
    obtain ⟨_,_,t,ht,hbin⟩ := hb
    have hrt : 0<t-r := hr.trans_le hbin.2.1.1
    have hd' := F.phaseHits_in_branch zX z (H:=H) inter_subset_right hh
    have he := F.branch_unique zX z hd' ⟨by linarith,(hJ ht).2⟩ hbin.1
    have hbin' := (inClosedConeBin_iff hrt).mp hbin
    rw [he] at ht hbin'
    exact ⟨ht,hbin'.2.2.2.2.1.1,hbin'.2.2.2.2.2.1.2⟩
  have ho := F.cone_occupation_angular_bound hT zX hs.f_smooth hs.vlasov
    (F.measurable_closedBinEulerian hs hT zX B hS hJ hC) inter_subset_right hd hD
    (fun z r hh=>(hmem z r hh).2.1) (fun z r hh=>(hmem z r hh).2.2)
    (by rintro z _ ⟨r,hr,rfl⟩; exact (hmem z r hr).1)
  refine ho.trans (mul_le_mul' le_rfl ?_)
  apply le_trans (lintegral_mono (fun z=>?_)) (hs.phase_energy_bound (left_mem_Icc.mpr hT))
  apply ENNReal.ofReal_le_ofReal
  exact le_mul_of_one_le_left (hs.nonnegative 0 (left_mem_Icc.mpr hT) z) (one_le_q z.2)

lemma PhaseFlowOn.closedEulerian_angular_time_budget {s : Solution} {T a b c d θ φ I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : 0<B.rmin) (hθ : 0<θ) (hφ : 0<φ) (hI : 0≤I) (hJI : b-a≤I)
    (hd : θ^2/2≤B.dmin) (hD : 0<B.Dmax) (hDhi : B.Dmax≤8*φ^2) :
    coneOccupation F.flow zX T s.f (closedBinEulerian F.flow zX T B S a b c d)≤
      ENNReal.ofReal (16*I*φ^2/θ^2)*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  have hd0 : 0<B.dmin := (by positivity : 0<θ^2/2).trans_le hd
  have ha := F.closedEulerian_time_budget hs hT zX B hS hJ hC hr hd0.le hD
  have hcoef : 0<B.dmin/B.Dmax := div_pos hd0 hD
  have hc : 0<ENNReal.ofReal (B.dmin/B.Dmax) := ENNReal.ofReal_pos.mpr hcoef
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (B.dmin/B.Dmax))⁻¹) ha
  rw [←mul_assoc,ENNReal.inv_mul_cancel hc.ne' ENNReal.ofReal_ne_top,one_mul] at hh
  rw [←mul_assoc] at hh
  refine hh.trans (mul_le_mul' ?_ le_rfl)
  rw [←ENNReal.ofReal_inv_of_pos hcoef,←ENNReal.ofReal_mul (inv_nonneg.mpr hcoef.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (B.dmin/B.Dmax)⁻¹*(b-a)≤(B.dmin/B.Dmax)⁻¹*I :=
      mul_le_mul_of_nonneg_left hJI (by positivity)
    _ = I*B.Dmax/B.dmin := by field_simp
    _ ≤ I*(8*φ^2)/(θ^2/2) := by gcongr
    _ = 16*I*φ^2/θ^2 := by ring

lemma Admissible.direct_source_time_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T → b-a≤I →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin → 0<B.Dmax →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let O := (ENNReal.ofReal (16*I*φ^2/θ^2)*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))) / ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hforce⟩ := hd₀.direct_source_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ hJI hI hp hP hθ hφ hσ
    hR hD hDmax hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  dsimp only
  have hforceBound := hforce s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ
    hI hp hP hθ hφ hσ hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T := by
    intro r hr
    exact ⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩
  have ho := F.closedEulerian_angular_time_budget hs hT zX B hS hJ hC hR hθ hφ hI.le hJI hdlo hDmax hDhi
  have hod : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) ≤
      (ENNReal.ofReal (16*I*φ^2/θ^2)*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) := by
    simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
  apply hforceBound.trans
  gcongr

lemma cone_relative_deficit_triangle (v w n : Vec) (hn : ‖n‖=1) :
    1-dot (velocity w) (velocity v)≤2*((1-dot n (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity v)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity w)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity v))) := by
  have hi := relative_angle_identity v w
  have hv := cone_angle_identity v n hn
  have hw := cone_angle_identity w n hn
  have hab : ‖velocity v-velocity w‖≤‖n-velocity v‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(n-velocity v)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(n-velocity v)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hna : ‖n-velocity v‖≤‖velocity v-velocity w‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(velocity v-velocity w)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(velocity v-velocity w)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hnb : ‖n-velocity w‖≤‖velocity v-velocity w‖+‖n-velocity v‖ := by
    calc
      _ = ‖(velocity v-velocity w)+(n-velocity v)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hsq {a b c : ℝ} (ha : 0≤a) (h : a≤b+c) : a^2≤2*(b^2+c^2) := by
    have hbc : 0≤b+c := ha.trans h
    have hh := mul_self_le_mul_self ha h
    nlinarith [sq_nonneg (b-c)]
  have hab2 := hsq (norm_nonneg _) hab
  have hna2 := hsq (norm_nonneg _) hna
  have hnb2 := hsq (norm_nonneg _) hnb
  refine ⟨?_,?_,?_⟩ <;>
    nlinarith [sq_nonneg ((q v)⁻¹),sq_nonneg ((q w)⁻¹)]

lemma cone_relative_bin_triangle {v w n : Vec} {θ φ σ : ℝ} (hn : ‖n‖=1)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) :
    σ^2≤32*(θ^2+φ^2) ∧ θ^2≤32*(σ^2+φ^2) ∧ φ^2≤32*(σ^2+θ^2) := by
  obtain ⟨he,hd,hD⟩ := cone_relative_deficit_triangle v w n hn
  constructor
  · linarith
  constructor <;> linarith

lemma cone_relative_bin_separated {v w n : Vec} {θ φ σ : ℝ}
    (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0≤σ) (hsep : 16*φ≤θ)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) : θ/8≤σ ∧ σ≤8*θ := by
  obtain ⟨he,hd,_⟩ := cone_relative_bin_triangle hn hdlo hdhi hDlo hDhi helo hehi
  have hsq := mul_self_le_mul_self (show 0≤16*φ by positivity) hsep
  constructor <;> nlinarith

lemma cone_relative_bin_upper {v w n : Vec} {θ φ σ κ : ℝ}
    (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0≤σ) (hκ : 0≤κ) (hsector : φ≤κ*θ)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) : σ≤8*(1+κ)*θ := by
  have hh := (cone_relative_bin_triangle hn hdlo hdhi hDlo hDhi helo hehi).1
  have hsq := mul_self_le_mul_self hφ hsector
  have hκθ : 0≤κ*θ^2 := mul_nonneg hκ (sq_nonneg θ)
  have hu : 0≤8*(1+κ)*θ := by positivity
  nlinarith [sq_nonneg (κ*θ)]

lemma cappedRepresentative_factor_eight {i j : ℕ}
    (hlo : cappedRepresentative i/8≤cappedRepresentative j)
    (hhi : cappedRepresentative j≤8*cappedRepresentative i) : j ≤ i+3 ∧ i ≤ j+3 := by
  have aux (a b : ℕ) (h : cappedRepresentative a/8≤cappedRepresentative b) : b≤a+3 := by
    by_contra hb
    have hab : a+4≤b := by omega
    have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤2⁻¹)
      (by norm_num : (2:ℝ)⁻¹≤1) hab
    rw [pow_add] at hp
    change cappedRepresentative b≤cappedRepresentative a*((2:ℝ)⁻¹)^4 at hp
    norm_num only [inv_pow,show (2:ℝ)^4=16 by norm_num] at hp
    nlinarith [cappedRepresentative_pos a]
  exact ⟨aux i j hlo,aux j i (by linarith)⟩

lemma cappedRepresentative_factor_eight_card (i N : ℕ) :
    ((Finset.range N).filter (fun j=>cappedRepresentative i/8≤cappedRepresentative j ∧
      cappedRepresentative j≤8*cappedRepresentative i)).card≤7 := by
  classical
  have hsub : (Finset.range N).filter (fun j=>cappedRepresentative i/8≤cappedRepresentative j ∧
      cappedRepresentative j≤8*cappedRepresentative i) ⊆ Finset.Icc (i-3) (i+3) := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have hh := cappedRepresentative_factor_eight h.1 h.2
    apply Finset.mem_Icc.mpr
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

lemma physical_relative_separated_index {T w t r : ℝ} {V : ℝ→Vec} {J : Set ℝ}
    {k : Fin 4→ℕ} {j : ℕ} {n : Sphere} {v : Vec}
    (hsep : 16*cappedRepresentative (k 2)≤cappedRepresentative (k 1))
    (hb : (t,r,n)∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n.1 (velocity (V t))) :
    j≤k 1+3 ∧ k 1≤j+3 := by
  have hh := cone_relative_bin_separated (v:=v) (w:=V t) (n:=n.1) (sphere_norm n)
    (cappedRepresentative_pos (k 1)).le (cappedRepresentative_pos (k 2)).le
    (cappedRepresentative_pos j).le hsep hv.2.1.1 hv.2.1.2
    hb.2.2.2.2.1 hb.2.2.2.2.2 hv.2.2.1 hv.2.2.2
  exact cappedRepresentative_factor_eight hh.1 hh.2

lemma capped_positive_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j/x)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.min' hne
    have hj₀ : j₀∈S := S.min'_mem hne
    have hjmin (j : ℕ) (hj : j∈S) : j₀≤j := S.min'_le j hj
    have hp (j : ℕ) (hj : j∈S) : cappedRepresentative j/x≤((2:ℝ)⁻¹)^(j-j₀) := by
      have he : cappedRepresentative j=cappedRepresentative j₀*((2:ℝ)⁻¹)^(j-j₀) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmin j hj)]
      rw [he]
      apply (div_le_iff₀ hx).mpr
      have hh := mul_le_mul_of_nonneg_right (hS j₀ hj₀)
        (pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) (j-j₀))
      simpa only [mul_comm] using hh
    have hpoint (j : ℕ) (hj : j∈S) : (cappedRepresentative j/x)^α≤(((2:ℝ)⁻¹)^α)^(j-j₀) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg (cappedRepresentative_pos j).le hx.le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j-j₀) S := by
      intro i hi j hj hij
      have hi' := hjmin i hi
      have hj' := hjmin j hj
      change i-j₀=j-j₀ at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j-j₀) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j-j₀),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma large_radius_magnetic_coefficient {H p ν θ φ : ℝ}
    (hH : 0<H) (hp : 0<p) (hν : 0<ν) (hθ : 0<θ) (hφ : 0<φ) :
    (H*p^2*ν^2*φ)^(1/3:ℝ)*(Real.sqrt p*ν/(θ*Real.sqrt H))^(2/3:ℝ)=
      p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity : 0≤H*p^2*ν^2) hφ.le,
    Real.mul_rpow (by positivity : 0≤H*p^2) (sq_nonneg ν),
    Real.mul_rpow hH.le (sq_nonneg p),
    Real.mul_rpow (Real.sqrt_nonneg p) hν.le,
    Real.mul_rpow hθ.le (Real.sqrt_nonneg H),
    Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast_mul hp.le,←Real.rpow_natCast_mul hν.le,
    ←Real.rpow_mul hp.le,←Real.rpow_mul hH.le,Real.rpow_neg hθ.le]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)*(1/3)=2/3 by norm_num,
    show (1/2:ℝ)*(2/3)=1/3 by norm_num]
  have hpp : p^(2/3:ℝ)*p^(1/3:ℝ)=p := by
    rw [←Real.rpow_add hp]; norm_num
  have hνν : ν^(2/3:ℝ)*ν^(2/3:ℝ)=ν^(4/3:ℝ) := by
    rw [←Real.rpow_add hν]; congr 1; norm_num
  have hHp : H^(1/3:ℝ)≠0 := (Real.rpow_pos_of_pos hH _).ne'
  have hθp : θ^(2/3:ℝ)≠0 := (Real.rpow_pos_of_pos hθ _).ne'
  calc
    _ = (p^(2/3:ℝ)*p^(1/3:ℝ))*(ν^(2/3:ℝ)*ν^(2/3:ℝ))*
        (θ^(2/3:ℝ))⁻¹*φ^(1/3:ℝ) := by field_simp [hHp,hθp]
    _ = _ := by rw [hpp,hνν]

lemma large_radius_magnetic_balance {H p θ φ σ : ℝ}
    (hH : 0<H) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0<σ) :
    let ν := min θ σ
    Summable (fun k : ℤ=>min (H*(2:ℝ)^k*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k)))) ∧
    (∑'k : ℤ,min (H*(2:ℝ)^k*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k))))≤
      dyadicBalanceConstant 1 (1/2)*(p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ)) := by
  dsimp only
  let ν := min θ σ
  have hν : 0<ν := lt_min hθ hσ
  let a := H*p^2*ν^2*φ
  let b := Real.sqrt p*ν/(θ*Real.sqrt H)
  have ha : 0<a := by dsimp only [a]; positivity
  have hb : 0<b := by dsimp only [b]; positivity
  have he (k : ℤ) : min (a*((2:ℝ)^k)^(1:ℝ)) (b*((2:ℝ)^k)^(-(1/2:ℝ)))=
      min (H*(2:ℝ)^k*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k))) := by
    rw [Real.rpow_one,Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
      ←Real.sqrt_eq_rpow,Real.sqrt_mul hH.le]
    dsimp only [a,b]
    congr 1 <;> ring
  have hs := dyadic_power_min_summable ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)
  have ht := dyadic_balance ha hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)
  simp_rw [he] at hs ht
  refine ⟨hs,?_⟩
  rw [show (1/2:ℝ)/(1+1/2)=1/3 by norm_num,
    show (1:ℝ)/(1+1/2)=2/3 by norm_num] at ht
  change _≤dyadicBalanceConstant 1 (1/2)*(a^(1/3:ℝ)*b^(2/3:ℝ)) at ht
  dsimp only [a,b] at ht
  rwa [large_radius_magnetic_coefficient hH hp hν hθ hφ] at ht

end RVM

end

end OAI
