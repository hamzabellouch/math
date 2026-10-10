import Mathlib
import OAI.Analysis.HardSphere.PathBounds.PathTailConstant
import OAI.Analysis.HardSphere.PathBounds.ExpNatTail

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice

lemma torusDistance_le_three_of_coord (L : Length) (x y : Torus L) {B : ℝ}
    (hB : 0≤B) (h : ∀ j, dist (x j) (y j)≤B) : torusDistance L x y≤3*B := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs : ∑ j : Fin 3, dist (x j) (y j)^2 ≤ ∑ _j : Fin 3, B^2 :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ dist_nonneg (h j) 2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num at hs
    nlinarith [sq_nonneg B]

lemma freeTrajectory_dist_le {n : ℕ} (L : Length) {t R : ℝ} (ht : t≤2) (hR : 0≤R)
    (w : CoordinatePaths n) (X : Configuration n L) (i : Fin n)
    (hw : ∀ j, ‖w (i,j)‖≤R) (u : Time) :
    torusDistance L (freeTrajectory n L t w X u i) (X i)≤6*R := by
  have hs : Real.sqrt (2*t)≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
  have hcoord (j : Fin 3) : dist (freeTrajectory n L t w X u i j) (X i j)≤2*R := by
    apply (freeTrajectory_coord_dist_le L t w X i u j).trans
    exact mul_le_mul hs (hw j) (norm_nonneg _) (by norm_num)
  have h := torusDistance_le_three_of_coord L _ _ (mul_nonneg (by norm_num) hR) hcoord
  nlinarith

attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def visitStartDistance {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (X : Configuration n L) : ℝ := by
  classical
  exact spatialSiteDistance L (A.image (siteCenter L)) (X i)

lemma visitStartDistance_nonneg {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (X : Configuration n L) : 0≤visitStartDistance L A i X :=
  spatialSiteDistance_nonneg _ _ _

lemma visit_distance_le {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (t : ℝ) (X : Configuration n L) (w : CoordinatePaths n)
    (hw : 0<visitCount L A i t X w) :
    ∃ u : Time, visitStartDistance L A i X≤
      torusDistance L (freeTrajectory n L t w X u i) (X i)+12 := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hw
  have hm : v∈A ∧ pathVisitsBall L 12 (siteCenter L v) i (freeTrajectory n L t w X) := by
    rw [pathVisitedSites] at hv
    exact Finset.mem_filter.mp hv
  obtain ⟨u,hu⟩ := hm.2
  have hd := spatialSiteDistance_le L (A.image (siteCenter L)) (X i) (siteCenter L v)
    (Finset.mem_image.mpr ⟨v,hm.1,rfl⟩)
  have htri := torusDistance_triangle' L (X i) (freeTrajectory n L t w X u i) (siteCenter L v)
  rw [torusDistance_comm L (X i) (freeTrajectory n L t w X u i)] at htri
  exact ⟨u,hd.trans (htri.trans (add_le_add le_rfl hu))⟩

lemma free_visit_travel_gaussian {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ}
    (ht : t≤2) (X : Configuration n L) (hd : 24≤visitStartDistance L A i X) :
    coordinateWiener n {w | 0<visitCount L A i t X w} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(visitStartDistance L A i X)^2/576)) := by
  let d := visitStartDistance L A i X
  let R := d/24
  have hR : 0≤R := div_nonneg (by dsimp [d]; linarith) (by norm_num)
  have hsub : {w | 0<visitCount L A i t X w} ⊆ ⋃ j : Fin 3, {w | R≤‖w (i,j)‖} := by
    intro w hw
    by_contra hn
    have hw' : ∀ j, ‖w (i,j)‖≤R := by
      have h : ∀ j, ‖w (i,j)‖<R := by simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
      exact fun j ↦ (h j).le
    obtain ⟨u,hu⟩ := visit_distance_le L A i t X w hw
    have hdist := freeTrajectory_dist_le L ht hR w X i hw' u
    dsimp [R,d] at hdist
    linarith
  have he (j : Fin 3) : coordinateWiener n {w | R≤‖w (i,j)‖} = wiener {w | R≤‖w‖} :=
    (measurePreserving_eval (fun _ : Direction n ↦ wiener) (i,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener n (⋃ j : Fin 3, {w | R≤‖w (i,j)‖}) := measure_mono hsub
    _ ≤ ∑' j : Fin 3, coordinateWiener n {w | R≤‖w (i,j)‖} := measure_iUnion_le _
    _ = 3*wiener {w | R≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*R^2))) := mul_le_mul_right (htail R hR) _
    _ = _ := by
      have he : -c*R^2 = -c*(visitStartDistance L A i X)^2/576 := by dsimp [R,d]; ring
      rw [he]; ac_rfl

theorem free_visit_travel : ∃ H : ℝ≥0∞, H<⊤ ∧
    ∀ {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
      (t : ℝ), t≤2 → ∀ X : Configuration n L,
      coordinateWiener n {w | 0<visitCount L A i t X w} ≤
        H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)) := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  let H := ENNReal.ofReal (Real.exp 72)+3*M*ENNReal.ofReal (Real.exp (1296/c))
  have hH : H<⊤ := by dsimp [H]; finiteness
  refine ⟨H,hH,?_⟩
  intro n K L A i t ht X
  let d := visitStartDistance L A i X
  by_cases hd : 24≤d
  · apply (free_visit_travel_gaussian htail L A i ht X hd).trans
    have hexp : -c*d^2/576 ≤ 1296/c+(-3*d) := by
      have hs := sq_nonneg (c*d-864)
      apply (mul_le_mul_iff_left₀ hc).mp
      have he : c*(1296/c)=1296 := mul_div_cancel₀ _ (ne_of_gt hc)
      nlinarith
    have hbound := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
    rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)] at hbound
    calc
      _ ≤ (3*M*ENNReal.ofReal (Real.exp (1296/c)))*ENNReal.ofReal (Real.exp (-3*d)) := by
        exact (mul_le_mul_right hbound (3*M)).trans_eq (by ring)
      _ ≤ _ := by gcongr; exact le_add_self
  · have he : 1≤ENNReal.ofReal (Real.exp 72)*ENNReal.ofReal (Real.exp (-3*d)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (by linarith))
    exact (prob_le_one).trans (he.trans (by gcongr; exact le_self_add))

end HardSphere.FreeVisits

namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

lemma lintegral_three_thirds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g h : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ w, f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ) ∂μ) ≤
    (∫⁻ w,f w ∂μ)^(1/3:ℝ)*(∫⁻ w,g w ∂μ)^(1/3:ℝ)*(∫⁻ w,h w ∂μ)^(1/3:ℝ) := by
  let F : Fin 3 → Ω → ℝ≥0∞ := ![f,g,h]
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) μ := by
    intro i _; fin_cases i <;> simp only [F] <;>
      first | exact hf.aemeasurable | exact hg.aemeasurable | exact hh.aemeasurable
  have H := ENNReal.lintegral_prod_norm_pow_le (μ:=μ) Finset.univ hF
    (p:=fun _ ↦ (1/3:ℝ)) (by norm_num) (by intros; norm_num)
  simpa [Fin.prod_univ_three,F] using H

lemma ofReal_exp_rpow {x p : ℝ} (hp : 0≤p) :
    ENNReal.ofReal (Real.exp x)^p = ENNReal.ofReal (Real.exp (x*p)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp,Real.exp_mul]

lemma indicator_one_third {Ω : Type*} (D : Set Ω) (w : Ω) :
    (D.indicator (fun _ ↦ (1:ℝ≥0∞)) w)^(1/3:ℝ) = D.indicator (fun _ ↦ 1) w := by
  classical
  by_cases hw : w∈D <;> simp [hw]

lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x-1≤x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [←Real.exp_add] at h
  simp only [neg_add_cancel,Real.exp_zero] at h
  nlinarith

def visitDefect {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) (D : Set (CoordinatePaths n)) (w : CoordinatePaths n) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (Real.exp (η*(if w∈D then (visitCount L A i t X w:ℝ) else 0))-1)

lemma visitDefect_le {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) {η η₀ : ℝ} (hη : 0≤η) (hηη : η≤η₀) (X : Configuration n L)
    (D : Set (CoordinatePaths n)) (w : CoordinatePaths n) :
    visitDefect L A i t η X D w ≤ ENNReal.ofReal η *
      (visitWeight L A i t (3*(η₀+1)) X w ^ (1/3:ℝ) *
      (D.indicator (fun _ ↦ (1:ℝ≥0∞)) w)^(1/3:ℝ) *
      ({w | 0<visitCount L A i t X w}.indicator (fun _ ↦ (1:ℝ≥0∞)) w) ^ (1/3:ℝ)) := by
  classical
  rw [indicator_one_third,indicator_one_third]
  by_cases hw : w∈D
  · by_cases hJ : 0<visitCount L A i t X w
    · have hJmem : w∈{w | 0<visitCount L A i t X w} := hJ
      simp only [Set.indicator_of_mem hw,Set.indicator_of_mem hJmem,mul_one]
      rw [visitWeight,ofReal_exp_rpow (by norm_num),←ENNReal.ofReal_mul hη]
      apply ENNReal.ofReal_le_ofReal
      simp only [ite_eq_left hw]
      set J : ℝ := (visitCount L A i t X w:ℝ)
      have hJe : J≤Real.exp J := by linarith [Real.add_one_le_exp J]
      have hJ0 : 0≤J := Nat.cast_nonneg _
      calc
        Real.exp (η*J)-1 ≤ (η*J)*Real.exp (η*J) := exp_sub_one_le_mul_exp _
        _ ≤ η*Real.exp J*Real.exp (η*J) := by gcongr
        _ = η*Real.exp ((η+1)*J) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
        _ ≤ η*Real.exp (3*(η₀+1)*J*(1/3)) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hη
          nlinarith
    · have hJ0 : visitCount L A i t X w=0 := Nat.eq_zero_of_not_pos hJ
      simp [visitDefect,hw,hJ0]
  · simp [visitDefect,hw]

theorem free_visit_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ≥0∞, C<⊤ ∧
    ∀ {n K : ℕ} [NeZero K] (L : Length), L.val=(K:ℝ) →
      ∀ (A : Finset (DiscreteTorus K)) (i : Fin n) {t η : ℝ}, 0<t → t≤2 →
      0≤η → η≤η₀ → ∀ (X : Configuration n L) (D : Set (CoordinatePaths n)),
      MeasurableSet D → ∀ ε : ℝ≥0∞, coordinateWiener n D≤ε →
      ∫⁻ w,visitDefect L A i t η X D w ∂coordinateWiener n ≤
        C*ENNReal.ofReal η*ε^(1/3:ℝ)*ENNReal.ofReal (Real.exp (-visitStartDistance L A i X)) := by
  obtain ⟨B,hB,hBM⟩ := free_visit_moment (3*(η₀+1)) (show 0≤3*(η₀+1) by positivity)
  obtain ⟨H,hH,hHT⟩ := free_visit_travel
  let C := B^(1/3:ℝ)*H^(1/3:ℝ)
  have hC : C<⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hH.ne)
  refine ⟨C,hC,?_⟩
  intro n K _ L hL A i t η ht ht2 hη hηη X D hD ε hε
  let V := {w | 0<visitCount L A i t X w}
  have hV : MeasurableSet V := measurableSet_lt measurable_const (visitCount_measurable L A i t X)
  let f := visitWeight L A i t (3*(η₀+1)) X
  let g := D.indicator (fun _ ↦ (1:ℝ≥0∞))
  let h := V.indicator (fun _ ↦ (1:ℝ≥0∞))
  have hf : Measurable f := visitWeight_measurable L A i t _ X
  have hg : Measurable g := measurable_const.indicator hD
  have hh : Measurable h := measurable_const.indicator hV
  have hm : Measurable (fun w ↦ f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ)) :=
    ((hf.pow_const _).mul (hg.pow_const _)).mul (hh.pow_const _)
  have hfb : (∫⁻ w,f w ∂coordinateWiener n)≤B := hBM L hL A i t (3*(η₀+1)) ht ht2 le_rfl X
  have hgb : (∫⁻ w,g w ∂coordinateWiener n)≤ε := by
    change (∫⁻ w,D.indicator 1 w ∂coordinateWiener n)≤ε
    rw [lintegral_indicator_one hD]; exact hε
  have hhb : (∫⁻ w,h w ∂coordinateWiener n)≤H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)) := by
    change (∫⁻ w,V.indicator 1 w ∂coordinateWiener n)≤_
    rw [lintegral_indicator_one hV]; exact hHT L A i t ht2 X
  calc
    _ ≤ ∫⁻ w,ENNReal.ofReal η*(f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ)) ∂coordinateWiener n :=
      lintegral_mono (visitDefect_le L A i t hη hηη X D)
    _ = ENNReal.ofReal η*(∫⁻ w,f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ) ∂coordinateWiener n) :=
      lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal η*((∫⁻ w,f w ∂coordinateWiener n)^(1/3:ℝ)*
        (∫⁻ w,g w ∂coordinateWiener n)^(1/3:ℝ)*(∫⁻ w,h w ∂coordinateWiener n)^(1/3:ℝ)) :=
      mul_le_mul_right (lintegral_three_thirds _ hf hg hh) _
    _ ≤ ENNReal.ofReal η*(B^(1/3:ℝ)*ε^(1/3:ℝ)*
        (H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)))^(1/3:ℝ)) := by
      gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ofReal_exp_rpow (by norm_num)]
      have he : -3*visitStartDistance L A i X*(1/3) = -visitStartDistance L A i X := by ring
      rw [he]; dsimp [C]; ring

end HardSphere.FreeVisits

end

end OAI
