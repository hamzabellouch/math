import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierMasterRegularityBarrier
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialEventBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSpatialNet_barrier_scope

open Set Metric
open scoped BigOperators

open CoulombAtom

def spatialGridIndex (h : ℝ) (x : Space) : Fin 3 → ℤ := fun i => ⌊x i / h⌋

lemma spatialGridIndex_close {h : ℝ} (hh : 0 < h) {x y : Space}
    (he : spatialGridIndex h x = spatialGridIndex h y) : ‖x-y‖ ≤ 3*h := by
  have hc (i : Fin 3) : |x i-y i| ≤ h := by
    have hi := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun he i)
    change |x i/h-y i/h| < 1 at hi
    rw [←sub_div,abs_div,abs_of_pos hh] at hi
    exact ((div_lt_one hh).mp hi).le
  have hs : ‖x-y‖^2 ≤ 3*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, h^2 := Finset.sum_le_sum (fun i _ => by
        change (x i-y i)^2 ≤ h^2
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i-y i)) hh.le).mpr (hc i))
      _ = _ := by simp
  nlinarith [norm_nonneg (x-y)]

lemma spatialGridIndex_bound {R h : ℝ} (hh : 0 < h)
    {x : Space} (hx : ‖x‖ ≤ R) (i : Fin 3) :
    spatialGridIndex h x i ∈ Finset.Icc (-(⌈R/h⌉₊+1 : ℕ):ℤ) (⌈R/h⌉₊+1 : ℕ) := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hi : |x i| ≤ R := hcoord.trans hx
  have hM : R/h < (⌈R/h⌉₊+1 : ℕ) := by
    have hh := Nat.le_ceil (R/h)
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  norm_num only [Nat.cast_add,Nat.cast_one] at hM
  simp only [Finset.mem_Icc,spatialGridIndex]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    have hxi := (abs_le.mp hi).1
    have hd : -R/h ≤ x i/h := div_le_div_of_nonneg_right hxi hh.le
    rw [neg_div] at hd
    linarith
  · apply Int.floor_le_iff.mpr
    push_cast
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (abs_le.mp hi).2 hh.le) (by linarith)

theorem exists_spatial_grid_net {A : Set Space} {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ Q : Finset Space, (∀ x ∈ Q, x ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ Q, ‖y-x‖ ≤ 3*h) ∧
      (Q.card:ℝ) ≤ (2*(R/h)+5)^3 := by
  classical
  let M : ℕ := ⌈R/h⌉₊+1
  let D : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(M:ℤ)) (M:ℤ))
  let E := D.filter (fun k => ∃ x ∈ A, spatialGridIndex h x = k)
  let f : (Fin 3 → ℤ) → Space := fun k => if hk : ∃ x ∈ A, spatialGridIndex h x = k then hk.choose else 0
  have hf {k : Fin 3 → ℤ} (hk : k ∈ E) : f k ∈ A ∧ spatialGridIndex h (f k) = k := by
    have he := (Finset.mem_filter.mp hk).2
    simpa only [f,dite_eq_left he] using he.choose_spec
  have hd {x : Space} (hx : x ∈ A) : spatialGridIndex h x ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,x,hx,rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact spatialGridIndex_bound hh (hA x hx) i
  refine ⟨E.image f,?_,?_,?_⟩
  · intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (hf hk).1
  · intro y hy
    refine ⟨f (spatialGridIndex h y),Finset.mem_image.mpr ⟨_,hd hy,rfl⟩,?_⟩
    apply spatialGridIndex_close hh
    exact (hf (hd hy)).2.symm
  · have hcard : (Finset.Icc (-(M:ℤ)) (M:ℤ)).card = 2*M+1 := by
      rw [Int.card_Icc]
      omega
    have hD : D.card = (2*M+1)^3 := by
      simp only [D,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have hM : (M:ℝ) ≤ R/h+2 := by
      have hm := Nat.ceil_lt_add_one (div_nonneg hR hh.le)
      dsimp [M]
      push_cast
      linarith
    calc
      _ ≤ (D.card:ℝ) := by exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le D _))
      _ = ((2*M+1:ℕ):ℝ)^3 := by rw [hD]; push_cast; rfl
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

theorem exists_initial_spatial_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ Q : Finset Space, (∀ x ∈ Q, ‖x‖ ≤ (11/10)*r) ∧
      (∀ y : Space, ‖y‖ ≤ (11/10)*r → ∃ x ∈ Q, ‖y-x‖ ≤ r^2) ∧
      (Q.card:ℝ) ≤ (12/r)^3 := by
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_spatial_grid_net (A := {x : Space | ‖x‖ ≤ (11/10)*r})
    (h := r^2/3) (by positivity) (by positivity) (fun _ hx => hx)
  refine ⟨Q,hQ,?_,hcard.trans ?_⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy
    refine ⟨x,hx,?_⟩
    nlinarith
  · apply pow_le_pow_left₀ (by positivity)
    have he : 2*((11/10)*r/(r^2/3))+5 = (33/5)/r+5 := by field_simp; ring
    rw [he]
    apply (le_div_iff₀ hr).mpr
    field_simp
    nlinarith

end Work_BarrierSpatialNet_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma finite_net_good_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m : MeasurableSpace Ω} (P : Ω → Space → ℝ)
    (Q : Finset Space) {A : Set Space} {θ p L d : ℝ}
    (hm : ∀ x ∈ Q, Measurable[m] (fun z => P z x))
    (hpoint : ∀ x ∈ Q, μ.real {z | θ < P z x} ≤ p)
    (hcover : ∀ y ∈ A, ∃ x ∈ Q, ‖y-x‖ ≤ d)
    (hQ : ∀ x ∈ Q, x ∈ A) (hL : 0 ≤ L)
    (hmod : ∀ z, ∀ x ∈ A, ∀ y ∈ A, |P z x-P z y| ≤ L*‖x-y‖) :
    ∃ G : Set Ω, MeasurableSet[m] G ∧
      (∀ z ∈ G, ∀ y ∈ A, P z y ≤ θ+L*d) ∧
      μ.real Gᶜ ≤ (Q.card:ℝ)*p := by
  classical
  let B : Set Ω := ⋃ x ∈ Q, {z | θ < P z x}
  refine ⟨Bᶜ,?_,?_,?_⟩
  · exact (Finset.measurableSet_biUnion Q (fun x hx => measurableSet_lt measurable_const (hm x hx))).compl
  · intro z hz y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy
    have hpx : P z x ≤ θ := by
      by_contra! hnot
      exact hz (mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,hnot⟩⟩)
    have hh := (le_abs_self (P z y-P z x)).trans (hmod z y hy x (hQ x hx))
    have hd := mul_le_mul_of_nonneg_left hxy hL
    linarith
  · rw [compl_compl]
    exact (measureReal_biUnion_finset_le Q _).trans (by
      calc
        _ ≤ ∑ _x ∈ Q, p := Finset.sum_le_sum hpoint
        _ = _ := by simp)

lemma initial_interpolation_exponent {r : ℝ} (hr : 0 < r) :
    r^(-2-3*masterExponent)*r^2*r = r^(1-3*masterExponent) := by
  rw [←Real.rpow_natCast,←Real.rpow_add hr]
  calc
    _ = r^((-2-3*masterExponent)+2)*r^(1:ℝ) := by rw [Real.rpow_one]; norm_num
    _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring

lemma initial_interpolation_bound {N : ℕ} {Z r c G : ℝ}
    (hcount : (N:ℝ) ≤ 3*Z) (hr : 0 < r) (hc : 0 < c) (hG : 0 ≤ G)
    (hsmall : (48*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent) ≤ 1/20) :
    (16*Real.pi*(N:ℝ)*G*c⁻¹^3)*r^(-2-3*masterExponent)*r^2 ≤ Z/(20*r) := by
  have hZ : 0 ≤ Z := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply (le_div_iff₀ (by positivity : 0 < 20*r)).mpr
  have he : ((16*Real.pi*(N:ℝ)*G*c⁻¹^3)*r^(-2-3*masterExponent)*r^2)*(20*r) =
      (N:ℝ)*(16*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent)*20 := by
    calc
      _ = (N:ℝ)*(16*Real.pi*G*c⁻¹^3)*(r^(-2-3*masterExponent)*r^2*r)*20 := by ring
      _ = _ := by rw [initial_interpolation_exponent hr]
  rw [he]
  calc
    _ ≤ (3*Z)*(16*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent)*20 := by gcongr
    _ = Z*((48*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent))*20 := by ring
    _ ≤ Z*(1/20)*20 := by gcongr
    _ = Z := by ring

lemma initial_net_probability {r : ℝ} (hr : 0 < r) :
    (12/r)^3*r^40 = 1728*r^37 := by
  field_simp
  ring

theorem actual_initial_good_event (Z : ℕ) (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (K j : ℕ) {δ G : ℝ} (hδ : 0 < δ)
    (hbudget : 3*(Z:ℝ)*lam+observationFisherConstant*r₀^(-2.02:ℝ)*
      (Real.log (Real.exp 1/r₀^40))^5+δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < (Z:ℝ)/(20*r₀))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    N ≤ 3*Z ∧ ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∃ A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
        MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j] A ∧
        (∀ z ∈ A, ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
          innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
            (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
              (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y ≤ (Z:ℝ)/(10*r₀)) ∧
        (physicalObservationLaw (graphRawLaw F) K).real Aᶜ ≤ 1728*r₀^37 := by
  obtain ⟨hcount,F,hn,hF,hpoint⟩ := actual_initial_pointwise_exceptional Z hZ hlam hr hs hs1 hc hc1 hN K j
    (pow_pos hr 40) hδ hbudget hsmall hg hcg hgn hrad hgs
  refine ⟨hcount,F,hn,hF,?_⟩
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P := fun z y => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let L := (16*Real.pi*(N:ℝ)*G*c₁⁻¹^3)*r₀^(-2-3*masterExponent)
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_initial_spatial_net hr hr1
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hm (y : Space) : Measurable[observationInformation ell j] (fun z => P z y) :=
    jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous
  obtain ⟨A,hA,hgood,hbad⟩ := finite_net_good_event (physicalObservationLaw (graphRawLaw F) K) P Q
    (A := {y : Space | ‖y‖ ≤ (11/10)*r₀}) (θ := (Z:ℝ)/(20*r₀)) (p := r₀^40) (L := L) (d := r₀^2)
    (fun y _ => hm y) (fun y hy => (hpoint y (hQ y hy)).le) hcover hQ (by dsimp [L]; positivity)
    (fun z x hx y hy => jointMasterPosterior_inner_difference (graphRawLaw F) ell j hc hr hs hrs hg.continuous hG _ x y hx hy)
  refine ⟨A,hA,?_,?_⟩
  · intro z hz y hy
    have hh := hgood z hz y hy
    have hi := initial_interpolation_bound (show (N:ℝ) ≤ 3*(Z:ℝ) by exact_mod_cast hcount) hr hc hGn hinterp
    change L*r₀^2 ≤ (Z:ℝ)/(20*r₀) at hi
    change P z y ≤ (Z:ℝ)/(10*r₀)
    have he : (Z:ℝ)/(10*r₀) = 2*((Z:ℝ)/(20*r₀)) := by ring
    rw [he]
    linarith
  · exact hbad.trans ((mul_le_mul_of_nonneg_right hcard (pow_nonneg hr.le 40)).trans_eq (initial_net_probability hr))

end CoulombBarrier

end

end OAI
