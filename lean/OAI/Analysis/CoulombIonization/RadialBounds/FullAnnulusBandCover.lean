import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ScaledSpatialInverse

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Set Metric

theorem exists_fullAnnulus_band_cover {B : ℝ} (hB : 1 ≤ B) :
    ∃ A : Finset ℝ, (∀ a ∈ A, 1/2 ≤ a) ∧
      ∀ t ∈ Icc 1 B, ∃ a ∈ A, 11*a/8 ≤ t ∧ t ≤ 13*a/8 := by
  classical
  let J := {q : ℝ // q ∈ Icc 1 B}
  have hc : Icc 1 B ⊆ ⋃ q : J, ball (q : ℝ) (1/32) := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,mem_ball_self (by norm_num)⟩
  obtain ⟨S,hS⟩ := isCompact_Icc.elim_finite_subcover
    (fun q : J => ball (q : ℝ) (1/32)) (fun _ => isOpen_ball) hc
  refine ⟨insert (2*B/3) (S.image (fun q : J => 2*(q:ℝ)/3)),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · linarith
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      linarith [q.property.1]
  · intro t ht
    obtain ⟨q,hq,hclose⟩ := mem_iUnion₂.mp (hS ht)
    have hd : |t-(q:ℝ)| < 1/32 := by simpa only [mem_ball,Real.dist_eq] using hclose
    refine ⟨2*(q:ℝ)/3,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q,hq,rfl⟩),?_,?_⟩
    · linarith [(abs_lt.mp hd).1,q.property.1]
    · linarith [(abs_lt.mp hd).2,q.property.1]

end
open MeasureTheory Filter Set
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem exists_actual_fullAnnulus_inverse_constant {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
          ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u → ∀ h ∈ Icc lo hi,
              (localTFResponse h < (localCellRadius y)^6*
                  originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
                h-xi ≤ (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
              ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                  localTFResponse h →
                (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                  16*(tfPatchCapConstant+3)) := by
  classical
  obtain ⟨A,hA,hcover⟩ := exists_fullAnnulus_band_cover hB
  let J := {a // a ∈ A}
  let : Fintype J := Fintype.ofFinite J
  choose C hC hresult using fun a : J =>
    exists_actual_scaled_spatial_inverse_constant (hA a a.property) hc hcL hlh hxi hlo
  let C₀ : ℝ := 1+∑ a : J, C a
  have hpos : 0 < C₀ := by
    dsimp [C₀]
    have := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset J)) => (hC a).le)
    linarith
  refine ⟨C₀,hpos,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have he : ∀ᶠ i in l, ∀ a : J, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
      ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
        MeasurableSet[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C a*((2:ℝ)^j.val*r₀ i)^37 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
          (∀ y : Space, 11*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 ≤ ‖y‖ →
            ‖y‖ ≤ 13*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 → ∀ h ∈ Icc lo hi,
            (localTFResponse h < (localCellRadius y)^6*
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
              h-xi ≤ (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
            ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                localTFResponse h →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
          (∀ y : Space, 11*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 ≤ ‖y‖ →
            ‖y‖ ≤ 13*((a:ℝ)*((2:ℝ)^j.val*r₀ i))/8 →
            (localCellRadius y)^4*
              originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                16*(tfPatchCapConstant+3)) := by
    exact Filter.eventually_all.mpr (fun a => hresult a hδ hs0 hr₀ hstate)
  filter_upwards [he,hr₀] with i hi hri
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hu : 0 < u := by dsimp [u]; positivity
  choose E hE hp hg using fun a : J => hi a j hjs
  refine ⟨⋃ a : J, E a,MeasurableSet.iUnion hE,?_,?_⟩
  · calc
      _ ≤ ∑ a : J, (physicalObservationLaw (graphRawLaw (F i)) (K i)).real (E a) :=
        measureReal_iUnion_fintype_le E
      _ ≤ ∑ a : J, C a*u^37 := Finset.sum_le_sum (fun a _ => hp a)
      _ ≤ C₀*u^37 := by rw [←Finset.sum_mul]; dsimp [C₀]; nlinarith [pow_nonneg hu.le 37]
  · have hall := Filter.eventually_all.mpr hg
    filter_upwards [hall] with q hq
    intro hqE
    have heq (a : J) : q ∉ E a := fun h => hqE (mem_iUnion.mpr ⟨a,h⟩)
    have hband (y : Space) (hyl : u ≤ ‖y‖) (hyh : ‖y‖ ≤ B*u) :
        ∃ a : J, 11*((a:ℝ)*u)/8 ≤ ‖y‖ ∧ ‖y‖ ≤ 13*((a:ℝ)*u)/8 := by
      have ht : ‖y‖/u ∈ Icc 1 B := ⟨(le_div_iff₀ hu).mpr (by simpa using hyl),
        (div_le_iff₀ hu).mpr hyh⟩
      obtain ⟨a,ha,hal,hah⟩ := hcover (‖y‖/u) ht
      refine ⟨⟨a,ha⟩,?_,?_⟩
      · have := (le_div_iff₀ hu).mp hal
        dsimp
        nlinarith
      · have := (div_le_iff₀ hu).mp hah
        dsimp
        nlinarith
    constructor
    · intro y hyl hyh h hh
      obtain ⟨a,hal,hah⟩ := hband y hyl hyh
      exact (hq a (heq a)).1 y hal hah h hh
    · intro y hyl hyh
      obtain ⟨a,hal,hah⟩ := hband y hyl hyh
      exact (hq a (heq a)).2 y hal hah

end CoulombAtom

end

end OAI
