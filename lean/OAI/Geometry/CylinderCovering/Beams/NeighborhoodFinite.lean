import OAI.Geometry.CylinderCovering.Beams.NeighborhoodArea
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodRiemann
import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace CylinderCovering.BeamNeighborhoodRealization
open RadialSweep RadialRiemann

lemma base_covers_parallel (D : Data) {a l r δ : ℝ}
    (hm : (l+r)/2 ∈ Icc D.α D.β) {q : Space}
    (hq : q ∈ rawBase D a l r δ) (t : ℝ) :
    q+t • (D.e+D.w ((l+r)/2)) ∈
      cylinder (direction D ((l+r)/2)) (base D a l r δ) := by
  let u := direction D ((l+r)/2)
  have hn : ‖D.e+D.w ((l+r)/2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (raw_direction_ne_zero D hm)
  have hparallel : t • (D.e+D.w ((l+r)/2)) =
      (t*‖D.e+D.w ((l+r)/2)‖) • u := by
    dsimp [u,direction]
    rw [smul_smul,mul_assoc,mul_inv_cancel₀ hn,mul_one]
  refine ⟨TriangularCovering.projection u q,⟨q,hq,rfl⟩,
    inner ℝ u q+t*‖D.e+D.w ((l+r)/2)‖,?_⟩
  rw [hparallel]
  unfold TriangularCovering.projection
  module

lemma minus_intercept_identity (a p m h t : ℝ) (ha : a ≤ 2) :
    physicalMap (ShortenedBeam.radialData a ha) (BeamNeighborhood.intercept a p m h t) +
      t • ((ShortenedBeam.radialData a ha).e+(ShortenedBeam.radialData a ha).w m) =
    ShortenedBeam.point (-1+h*p+t*(1-a*(2-a)*p^2))
      (-1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2)) t := by
  ext i
  fin_cases i <;> simp [physicalMap,ShortenedBeam.radialData,ShortenedBeam.velocity,
    ShortenedBeam.point,BeamNeighborhood.intercept,BeamNeighborhood.radial,
    BeamNeighborhood.velocity] <;> ring

lemma plus_intercept_identity (a p m h t : ℝ) (ha : a ≤ 2) :
    physicalMap (ShortenedBeam.radialDataPlus a ha) (BeamNeighborhood.intercept a p m h t) +
      t • ((ShortenedBeam.radialDataPlus a ha).e+(ShortenedBeam.radialDataPlus a ha).w m) =
    ShortenedBeam.point (-(-1+h*p+t*(1-a*(2-a)*p^2)))
      (-(-1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2))) t := by
  ext i
  fin_cases i <;> simp [physicalMap,ShortenedBeam.radialDataPlus,ShortenedBeam.velocity,
    ShortenedBeam.point,BeamNeighborhood.intercept,BeamNeighborhood.radial,
    BeamNeighborhood.velocity] <;> ring

lemma midpoint_tagged (N : ℕ) :
    IsTagged 0 1 N (fun i => (point 0 1 N i+point 0 1 N (i+1))/2) := by
  intro i
  have hp := point_succ 0 1 N i
  have hd := step_pos (by norm_num : (0:ℝ)<1) (Nat.zero_lt_of_lt i.isLt)
  constructor <;> linarith

theorem cellBase_covers_minus {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    {N : ℕ} (hN : 0 < N) :
    ∀ z ∈ ShortenedBeam.beamMinus a, ∃ i : Fin N,
      z ∈ cylinder
        (direction (ShortenedBeam.radialData a (by linarith))
          ((point 0 1 N i+point 0 1 N (i+1))/2))
        (cellBase (ShortenedBeam.radialData a (by linarith)) a N i) := by
  rintro z ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
  obtain ⟨i,hi⟩ := exists_cell hN (show p ∈ Icc (0:ℝ) 1 from ⟨hp0,hp1⟩)
  refine ⟨i,?_⟩
  have hm := cell_subset (by norm_num : (0:ℝ)<1) i (midpoint_tagged N i)
  have hinter := BeamNeighborhood.intercept_mem_paddedSector ha ha1
    (step_pos (by norm_num : (0:ℝ)<1) hN).le (point_succ 0 1 N i)
    hi ⟨hh0,hh1⟩ ht
  have hc := base_covers_parallel (ShortenedBeam.radialData a (by linarith)) hm
    (q := physicalMap (ShortenedBeam.radialData a (by linarith))
      (BeamNeighborhood.intercept a p ((point 0 1 N i+point 0 1 N (i+1))/2) h t))
    ⟨_,hinter,rfl⟩ t
  rw [minus_intercept_identity,← hx,← hy,← hz] at hc
  exact hc

theorem cellBase_covers_plus {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    {N : ℕ} (hN : 0 < N) :
    ∀ z ∈ ShortenedBeam.beamPlus a, ∃ i : Fin N,
      z ∈ cylinder
        (direction (ShortenedBeam.radialDataPlus a (by linarith))
          ((point 0 1 N i+point 0 1 N (i+1))/2))
        (cellBase (ShortenedBeam.radialDataPlus a (by linarith)) a N i) := by
  rintro z ⟨x,y,t,ht,⟨p,h,hp0,hp1,hh0,hh1,hx,hy⟩,hz⟩
  obtain ⟨i,hi⟩ := exists_cell hN (show p ∈ Icc (0:ℝ) 1 from ⟨hp0,hp1⟩)
  refine ⟨i,?_⟩
  have hm := cell_subset (by norm_num : (0:ℝ)<1) i (midpoint_tagged N i)
  have hinter := BeamNeighborhood.intercept_mem_paddedSector ha ha1
    (step_pos (by norm_num : (0:ℝ)<1) hN).le (point_succ 0 1 N i)
    hi ⟨hh0,hh1⟩ ht
  have hc := base_covers_parallel (ShortenedBeam.radialDataPlus a (by linarith)) hm
    (q := physicalMap (ShortenedBeam.radialDataPlus a (by linarith))
      (BeamNeighborhood.intercept a p ((point 0 1 N i+point 0 1 N (i+1))/2) h t))
    ⟨_,hinter,rfl⟩ t
  rw [plus_intercept_identity,← hx,← hy] at hc
  simpa only [cellBase,neg_neg,← hz] using hc

lemma step_le_one {N : ℕ} (hN : 0 < N) : step 0 1 N ≤ 1 := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  simp only [step,sub_zero]
  exact (div_le_one (by positivity)).mpr hNr

lemma cellBase_estimates (D : Data) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hα : D.α=0) (hβ : D.β=1) (hκ : kappa D=1/2)
    (hw : ∀ p, ‖D.w p‖=‖ShortenedBeam.velocity a p‖)
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    Measure.euclideanHausdorffMeasure 2 (cellBase D a N i) ≠ ⊤ ∧
    TriangularCovering.area (cellBase D a N i) ≤
      (2-a)^2/4*(step 0 1 N*(1/Real.sqrt (1+‖ShortenedBeam.velocity a (cellMidpoint N i)‖^2)))+
        56*(step 0 1 N)^2 := by
  have hm : cellMidpoint N i ∈ Icc D.α D.β := by
    rw [hα,hβ]
    exact cell_subset (by norm_num) i (midpoint_tagged N i)
  have hh := base_area_le D ha ha1
    (point_mem (by norm_num : (0:ℝ)<1) hN i.isLt.le).1
    (point_mem (by norm_num : (0:ℝ)<1) hN (Nat.succ_le_of_lt i.isLt)).2
    (step_pos (by norm_num : (0:ℝ)<1) hN) (step_le_one hN) (point_succ 0 1 N i) hm
  refine ⟨hh.1,?_⟩
  rw [hκ,hw] at hh
  have hs : 1 ≤ Real.sqrt (1+‖ShortenedBeam.velocity a (cellMidpoint N i)‖^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg ‖ShortenedBeam.velocity a (cellMidpoint N i)‖]
  have hb := padded_radius_area_bound (N:=2-a) (by linarith) (by linarith)
    (step_pos (by norm_num : (0:ℝ)<1) hN).le (step_le_one hN) hs
  have heq : (1/2:ℝ)*step 0 1 N*(2-a+11*step 0 1 N+2*(step 0 1 N)^2)^2/
      (2*Real.sqrt (1+‖ShortenedBeam.velocity a (cellMidpoint N i)‖^2)) =
      step 0 1 N*(2-a+11*step 0 1 N+2*(step 0 1 N)^2)^2/
      (4*Real.sqrt (1+‖ShortenedBeam.velocity a (cellMidpoint N i)‖^2)) := by ring
  calc
    _ ≤ _ := hh.2
    _ = _ := heq
    _ ≤ _ := hb
    _ = _ := by ring

lemma cost_bound (D : Data) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hα : D.α=0) (hβ : D.β=1) (hκ : kappa D=1/2)
    (hw : ∀ p, ‖D.w p‖=‖ShortenedBeam.velocity a p‖) {K : NNReal}
    (hK : LipschitzOnWith K (fun p => 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)) (Icc (0:ℝ) 1))
    {N : ℕ} (hN : 0 < N) :
    cost D a N ≤ (2-a)^2/4*(∫ p in (0:ℝ)..1, 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2))+
      ((2-a)^2*(K:ℝ)/4+56)*step 0 1 N := by
  apply summed_padding_bound hK hN (cellMidpoint N) (midpoint_tagged N)
    (fun i => TriangularCovering.area (cellBase D a N i)) (2-a)
  exact fun i => (cellBase_estimates D ha ha1 hα hβ hκ hw hN i).2

lemma oneBeam_integral_eq (a : ℝ) (ha : a ≤ 2) :
    (2-a)^2/4*(∫ p in (0:ℝ)..1, 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)) =
      (Real.sqrt 2/8)*BeamCost.beamCost a := by
  rw [← ShortenedBeam.radialData_weightedArea a ha]
  unfold weightedArea
  rw [ShortenedBeam.radialData_kappa]
  change _ = (1/2:ℝ)*(∫ p in (0:ℝ)..1, (2-a)^2/(2*Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)))
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  ring

lemma beamBaseMinus_eq (a : ℝ) (ha : a ≤ 2) (N : ℕ) (i : Fin N) :
    beamBaseMinus a N i=cellBase (ShortenedBeam.radialData a ha) a N i := by
  unfold beamBaseMinus cellBase base rawBase
  congr 2
  funext z
  ext j
  fin_cases j <;> simp [physicalMap,ShortenedBeam.radialData,ShortenedBeam.point] <;> ring

lemma beamBasePlus_eq (a : ℝ) (ha : a ≤ 2) (N : ℕ) (i : Fin N) :
    beamBasePlus a N i=cellBase (ShortenedBeam.radialDataPlus a ha) a N i := by
  unfold beamBasePlus cellBase base rawBase
  congr 2
  funext z
  ext j
  fin_cases j <;> simp [physicalMap,ShortenedBeam.radialDataPlus,ShortenedBeam.point] <;> ring

theorem alternativeStatement : AlternativeStatement := by
  intro a ha ha1
  have ha2 : a ≤ 2 := by linarith
  obtain ⟨K,hK⟩ := beamWeight_lipschitz a
  let γ : ℝ := (2-a)^2*(K:ℝ)/4+56
  refine ⟨2*γ,by dsimp [γ]; positivity,?_⟩
  intro N hN
  have hm (i : Fin N) : cellMidpoint N i ∈ Icc (0:ℝ) 1 :=
    cell_subset (by norm_num) i (midpoint_tagged N i)
  have hwplus : ∀ p, ‖(ShortenedBeam.radialDataPlus a ha2).w p‖=‖ShortenedBeam.velocity a p‖ := by
    intro p
    exact norm_neg _
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [beamBaseMinus_eq a ha2,beamBasePlus_eq a ha2]
    rw [← ShortenedBeam.radialData_direction a (cellMidpoint N i) ha2,
      ← ShortenedBeam.radialDataPlus_direction a (cellMidpoint N i) ha2]
    have hum := actual_direction_unit (ShortenedBeam.radialData a ha2) (hm i)
    have hup := actual_direction_unit (ShortenedBeam.radialDataPlus a ha2) (hm i)
    have hcm := base_compact (ShortenedBeam.radialData a ha2) a
      (point 0 1 N i) (point 0 1 N (i+1)) (step 0 1 N)
    have hcp := base_compact (ShortenedBeam.radialDataPlus a ha2) a
      (point 0 1 N i) (point 0 1 N (i+1)) (step 0 1 N)
    exact ⟨hum,hup,hcm,hcp,hcm.measurableSet,hcp.measurableSet,
      (cellBase_estimates (ShortenedBeam.radialData a ha2) ha.le ha1.le rfl rfl
        (ShortenedBeam.radialData_kappa a ha2) (fun _ => rfl) hN i).1,
      (cellBase_estimates (ShortenedBeam.radialDataPlus a ha2) ha.le ha1.le rfl rfl
        (ShortenedBeam.radialDataPlus_kappa a ha2) hwplus hN i).1,
      base_perpendicular (ShortenedBeam.radialData a ha2) a _ _ _ hum,
      base_perpendicular (ShortenedBeam.radialDataPlus a ha2) a _ _ _ hup⟩
  · simpa only [cellMidpoint,beamBaseMinus_eq a ha2,← ShortenedBeam.radialData_direction a _ ha2]
      using cellBase_covers_minus ha.le ha1.le hN
  · simpa only [cellMidpoint,beamBasePlus_eq a ha2,← ShortenedBeam.radialDataPlus_direction a _ ha2]
      using cellBase_covers_plus ha.le ha1.le hN
  · have hcm := cost_bound (ShortenedBeam.radialData a ha2) ha.le ha1.le rfl rfl
      (ShortenedBeam.radialData_kappa a ha2) (fun _ => rfl) hK hN
    have hcp := cost_bound (ShortenedBeam.radialDataPlus a ha2) ha.le ha1.le rfl rfl
      (ShortenedBeam.radialDataPlus_kappa a ha2) hwplus hK hN
    rw [oneBeam_integral_eq a ha2] at hcm hcp
    unfold alternativeCost
    simp_rw [beamBaseMinus_eq a ha2,beamBasePlus_eq a ha2]
    change cost (ShortenedBeam.radialData a ha2) a N+
      cost (ShortenedBeam.radialDataPlus a ha2) a N ≤ _
    calc
      _ ≤ ((Real.sqrt 2/8)*BeamCost.beamCost a+γ*step 0 1 N)+
          ((Real.sqrt 2/8)*BeamCost.beamCost a+γ*step 0 1 N) := add_le_add hcm hcp
      _ = _ := by unfold step; ring

end CylinderCovering.BeamNeighborhoodRealization

end

end OAI
