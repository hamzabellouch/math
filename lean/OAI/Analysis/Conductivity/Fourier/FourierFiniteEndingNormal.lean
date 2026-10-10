import Mathlib
import OAI.Analysis.Conductivity.Branching.MatchedEndingWeak
import OAI.Analysis.Conductivity.Fourier.EndingJoinPeriodicity
import OAI.Analysis.Conductivity.Branching.MatchedEndingRegularity

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

local instance fourierFiniteEndingNormalMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance fourierFiniteEndingNormalBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem aligned_fourier_finite_ending_with_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : 0<k) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0<c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∃ hsym : ∀ x,(E x).IsSymm,
          ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion v (fun y => ⟨E y,hsym y⟩) {y : Coord3 | 0<y 0}) ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor s) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → E x*ᵥPi.single 0 1=Pi.single 0 1) ∧
        (∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ v x)).col) ∧
        (∃ G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ, ContDiff ℝ 1 G ∧
          ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x) ∧
        ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
          tsupport ψ.val ⊆ {x : Coord3 | 0<x 0} →
          Integrable (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x) ∧
          (∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have hk0 : k≠0 := ne_of_gt hk
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  let lam := torusRate s ![0,k]
  have hlam : 0<lam := axial_torusRate_pos hs hk0
  obtain ⟨p,hp,hpδ,u,D,hus,hDs,hup,hDp,hDsym,hDb,hPDE,hDflat,huin,huout,hurank⟩ :=
    elliptic_fourier_matching_regular (pa:=pa) hs hk0 hA hB ha hb hga hgb hra hrb hpb hδ
  obtain ⟨J,L,K,ce,Ce,hJ,hL,hK,hce,hceCe,he⟩ := exists_finiteEnding_parameters (div_pos hlam hkr)
  let c := min (1/4) ce
  let C := max (3*‖flatBackgroundTensor s‖+1) Ce
  let T := 7+(J+2+2*cascadeLength L K)/(k:ℝ)
  have hl : 0<cascadeLength L K := cascade_length_positive (by linarith) hK
  have hT : 7<T := by dsimp [T]; linarith [div_pos (show 0<J+2+2*cascadeLength L K by linarith) hkr]
  have hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos ((k:ℝ)*x 2)] := by
    intro x hx
    rw [huout x hx]
    congr 1
    simp [flatPhaseMode,torusAngular,lam]
  have hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s := by
    intro x hx
    apply hDflat x
    intro hh
    linarith [hh.2,hx.1]
  have hDb' : ∀ x w : Coord3,c*(w ⬝ᵥ w)≤w ⬝ᵥ(D x*ᵥw) ∧ w ⬝ᵥ(D x*ᵥw)≤C*(w ⬝ᵥ w) := by
    intro x w
    have hw : 0≤w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hw).trans (hDb x w).1,
      (hDb x w).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)⟩
  have he' : ∀ x w : Coord3,c*(w ⬝ᵥ w)≤w ⬝ᵥ(alignedEndingTensor lam k J L K x*ᵥw) ∧
      w ⬝ᵥ(alignedEndingTensor lam k J L K x*ᵥw)≤C*(w ⬝ᵥ w) := by
    intro x w
    have hw : 0≤w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hh := alignedEndingTensor_bounds he x w
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hw).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)⟩
  have hDmeas : Measurable D := by
    apply Measurable.of_eval; intro i
    apply Measurable.of_eval; intro j
    exact ((continuous_apply j).comp ((continuous_apply i).comp hDs.continuous)).measurable
  refine ⟨p,T,c,C,hp,hpδ,hT,lt_min (by norm_num) hce,
    (min_le_right _ _).trans (hceCe.trans (le_max_right _ _)),
    matchedEndingPair u lam k J L K,endingJoinTensor D lam k J L K,
    matchedEndingPair_C2 (hus.of_le (show (2:WithTop ℕ∞)≤↑(⊤:ℕ∞) by norm_cast)) hkr hJ hL hK hum,
    endingJoinTensor_measurable hDmeas _ _ _ _ _,
    matchedEndingPair_periodic hup _ _ _ _ _,endingJoinTensor_periodic hDp _ _ _ _ _,
    ?_,endingJoinTensor_bounds hDb' he',?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨endingJoinTensor_symm hDsym _ _ _ _ _,?_⟩
    exact matchedEnding_regularRegion_ae hDs hus hDsym hkr hJ (by linarith) hK hum hDm hurank
      (isOpen_lt continuous_const (continuous_apply 0)) (Subset.refl _)
  · intro x hx
    rw [matchedEndingPair,ite_eq_left (by linarith [hx.2])]
    exact huin x hx
  · intro x hx
    rw [endingJoinTensor_left _ _ _ _ _ _ _ (by linarith [hx.2])]
    by_cases hh : x 0<1/2
    · exact hDflat x (fun h => (not_le.mpr hh) h.1)
    have heq : x 0=1/2 := le_antisymm hx.2 (le_of_not_gt hh)

    have hnear : ∀ᶠ y in 𝓝[<] (1/2:ℝ),D (Function.update x 0 y)=flatBackgroundTensor s := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      apply hDflat
      simpa using (show y∉Icc (1/2:ℝ) (11/2) from fun h => (not_le.mpr hy) h.1)
    have hlim : Tendsto (fun y : ℝ => D (Function.update x 0 y)) (𝓝[<] (1/2:ℝ)) (𝓝 (D x)) := by
      have hupp : Continuous (fun y : ℝ => Function.update x 0 y) := by
        apply continuous_pi
        intro i
        by_cases hi : i=0
        · subst i
          change Continuous (fun y : ℝ => y)
          exact continuous_id
        · simpa [Function.update_of_ne hi] using (continuous_const : Continuous (fun _ : ℝ => x i))
      have hc : Continuous (fun y : ℝ => D (Function.update x 0 y)) := hDs.continuous.comp hupp
      have := (hc.tendsto (1/2)).mono_left (nhdsWithin_le_nhds (s:=Iio (1/2:ℝ)))
      simpa only [←heq,Function.update_eq_self] using this
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hnear))
  · intro x hx
    apply matchedEndingPair_terminal hJ hL hK x (by linarith)
    have hh : (J+2+2*cascadeLength L K)/(k:ℝ)≤x 0-7 := by dsimp [T] at hx; linarith
    simpa only [mul_comm] using (div_le_iff₀ hkr).mp hh
  · intro x hx
    rw [endingJoinTensor_right _ _ _ _ _ _ _ hx]
    exact alignedEndingTensor_normal _ _ _ _ _ _
  · filter_upwards [hurank] with x hx
    intro hbnd
    rw [matchedEndingPair_left_deriv (by linarith [hbnd.2])]
    exact hx hbnd
  · refine ⟨(fun x i j => joinedFlux D u lam k J L K j x i),?_,?_⟩
    · exact contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
        contDiff_pi.mp (joinedFlux_C1 hDs hus hJ hL hK j) i))
    · filter_upwards [endingJoin_constitution_ae (D:=D) hkr hJ hL hK hum] with x hx
      ext i j
      exact congrFun (hx j) i
  · intro j ψ hcψ hsψ
    exact matchedEnding_weak_equation hDs hus hkr hJ hL hK hum hDm hPDE j ψ hcψ hsψ

end ScalarConductivity

end
end

end OAI
