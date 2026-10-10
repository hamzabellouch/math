import OAI.Geometry.LatticeCovering.Rates

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Horizontal
open MeasureTheory Completion
open scoped ENNReal BigOperators



structure FullLattice (m : ℕ) where
  module : Submodule ℤ (Fin m → ℝ)
  discrete : DiscreteTopology module
  full : IsZLattice ℝ module

attribute [instance] FullLattice.discrete FullLattice.full

namespace FullLattice

def hole {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ)) : ℝ≥0∞ :=
  torusMeasure m ((latticeProjection L.module '' J)ᶜ)

end FullLattice




theorem common_horizontal_from_mean {m : ℕ} {X α : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (family : X → FullLattice m)
    (J : α → Set (Fin m → ℝ)) (s : Finset α) (Dh CR η τ N : ℝ)
    (hCR : 0 ≤ CR) (hDh : 0 < Dh)
    (hcov : ∀ x, ZLattice.covolume (family x).module=Dh)
    (hmeas : ∀ a ∈ s, Measurable (fun x => (family x).hole (J a)))
    (hmean : ∀ a ∈ s, ∫⁻ x, (family x).hole (J a) ∂μ ≤
      ENNReal.ofReal (Real.exp (-(volume (J a)).toReal/Dh)+CR*Real.exp (-η)))
    (hlo : ∀ a ∈ s, τ ≤ (volume (J a)).toReal/Dh)
    (hhi : ∀ a ∈ s, (volume (J a)).toReal/Dh ≤ η)
    (hcard : (s.card : ℝ) ≤ N)
    (hcriterion : (1+CR)*N*Real.exp (-τ/2)<1) :
    ∃ L : FullLattice m, ZLattice.covolume L.module=Dh ∧
      ∀ a ∈ s, L.hole (J a) ≤ ENNReal.ofReal (Real.exp (-((volume (J a)).toReal/Dh)/2)) := by
  have _ := hDh
  have hsum : (1+CR)*(∑ a ∈ s, Real.exp (-((volume (J a)).toReal/Dh)/2))<1 := by
    apply lt_of_le_of_lt _ hcriterion
    calc
      _ ≤ (1+CR)*(∑ a ∈ s, Real.exp (-τ/2)) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun a ha => Real.exp_le_exp.mpr (by linarith [hlo a ha]))) (by linarith)
      _ = (1+CR)*(s.card : ℝ)*Real.exp (-τ/2) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by linarith)) (Real.exp_pos _).le
  obtain ⟨x,hx⟩ := common_hole_sample μ s (fun a x => (family x).hole (J a))
    (fun a => (volume (J a)).toReal/Dh) CR η hCR hmeas hhi (by
      intro a ha
      simpa only [neg_div] using hmean a ha) hsum
  exact ⟨family x,hcov x,hx⟩


end SingleLatticeCovering.Horizontal

end
end

section


noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open scoped BigOperators Pointwise ENNReal






theorem sections_and_mean_cover {B : Block} (c : Chain B) {m : ℕ}
    (hm : 2 ≤ m) (hD : 0 < c.fullDim)
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hgauss : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
      (volume K).toReal*gamma y/2 ≤ (volume (coordinateFiber K y)).toReal)
    (κ ρ ε τ A CR : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hA : 0 < A) (hCR : 0 ≤ CR)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ (Real.exp (-1)/8)*κ*ρ)
    (hcap : (Real.exp 1/8)*ρ*ε ≤ FinalRates.eta m)
    (hcriterion : (1+CR)*(3*(m : ℝ)^2)^c.fullDim*Real.exp (-τ/2)<1)
    (hcount : ∀ {α : Type} (s : Finset α), (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim →
      let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
      1 ≤ Lstar ∧ (patternTotal c.alphabetSeq s c.fullDim : ℝ)<Lstar ∧
      Real.exp ((2 : ℝ)^c.fullDim*Real.log Lstar-A/2) ≤
        1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim)))
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (family : X → FullLattice m)
    (hcov : ∀ x, ZLattice.covolume (family x).module volume=(volume K).toReal/(ρ*c.det))
    (hmeas : ∀ J : Set (Fin m → ℝ), IsCompact J → Convex ℝ J → (interior J).Nonempty →
      Measurable (fun x => (family x).hole J))
    (hmean : ∀ J : Set (Fin m → ℝ), IsCompact J → Convex ℝ J → (interior J).Nonempty →
      (volume J).toReal/((volume K).toReal/(ρ*c.det)) ≤ FinalRates.eta m →
      ∫⁻ x, (family x).hole J ∂μ ≤
        ENNReal.ofReal (Real.exp (-(volume J).toReal/((volume K).toReal/(ρ*c.det)))+
          CR*Real.exp (-FinalRates.eta m))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  classical
  let Dh := (volume K).toReal/(ρ*c.det)
  have hDh : 0 < Dh := div_pos hV (mul_pos hρ c.det_pos)
  obtain ⟨e,heK,heconv,hevol,S,hSc,J,hJ,hsections⟩ :=
    coordinate_marginal_to_labels hm hD hK hconv hV hR hsmall hgauss
  let α := {a // a ∈ S}
  let J' : α → Set (Fin m → ℝ) := fun a => J a.val
  let u : α → ℝ := fun a => (volume (J' a)).toReal/Dh
  let s : Finset α := Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ (Real.exp 1/8)*ρ*ε)
  have hcard : (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim := by
    have hh : s.card ≤ S.card := by
      calc
        s.card ≤ (Finset.univ : Finset α).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = S.card := by simp [α]
    exact (by exact_mod_cast hh : (s.card : ℝ) ≤ S.card).trans hSc
  have hulo (a : α) (ha : a ∈ s) : τ ≤ u a := (Finset.mem_filter.mp ha).2.1
  have huhi (a : α) (ha : a ∈ s) : u a ≤ FinalRates.eta m :=
    ((Finset.mem_filter.mp ha).2.2).trans hcap
  obtain ⟨L,hLc,hLhole⟩ := common_horizontal_from_mean μ family J' s Dh CR
    (FinalRates.eta m) τ ((3*(m : ℝ)^2)^c.fullDim) hCR hDh hcov (by
      intro a ha
      exact hmeas (J' a) (hJ a.val a.property).1 (hJ a.val a.property).2.1 (hJ a.val a.property).2.2)
    (by
      intro a ha
      exact hmean (J' a) (hJ a.val a.property).1 (hJ a.val a.property).2.1
        (hJ a.val a.property).2.2 (huhi a ha)) hulo huhi hcard hcriterion
  let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
  obtain ⟨hLstar,hcost,herror⟩ := hcount s hcard
  have hV' : 0 < (volume (e '' K)).toReal := by rwa [hevol]
  have hcov' : ZLattice.covolume L.module volume=(volume (e '' K)).toReal/(ρ*c.det) := by
    rw [hevol]; exact hLc
  obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := labeled_chain_to_cover c (by omega) L.module (e '' K)
    heK heconv hV' J' (fun a => (hJ a.val a.property).1)
    κ ρ (Real.exp (-1)/8) (Real.exp 1/8) ε τ A Lstar hρ (by positivity) (by positivity)
    hτ hA hcov' hpat (by
      intro v hv
      obtain ⟨a,ha,hin,hl,hu⟩ := hsections v (hv.trans hrad)
      exact ⟨⟨a,ha⟩,hin,hl,hu⟩) (by
      intro a hlo hhi
      have ha : a ∈ s := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_,?_⟩
        · simpa only [hLc] using hlo
        · simpa only [hLc] using hhi
      simpa only [FullLattice.hole,hLc] using hLhole a ha) hload hLstar (by
      simpa only [hLc,s,u,patternTotal,Lstar] using hcost) (by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using herror)
  let := hd
  let := hfull
  exact pull_back_cover e K Λ hcover hbound


end SingleLatticeCovering.Assembly

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open MeasureTheory Completion Horizontal Sections
open scoped ENNReal




structure MeanHoleModel (m : ℕ) (Dh CR : ℝ) where
  Sample : Type
  measurable : MeasurableSpace Sample
  measure : @Measure Sample measurable
  probability : @IsProbabilityMeasure Sample measurable measure
  lattice : Sample → FullLattice m
  covolume : ∀ x, ZLattice.covolume (lattice x).module volume=Dh
  measurable_hole : letI := measurable
    ∀ J : Set (Fin m → ℝ), IsCompact J → Convex ℝ J → (interior J).Nonempty →
      Measurable (fun x => (lattice x).hole J)
  mean : letI := measurable
    ∀ J : Set (Fin m → ℝ), IsCompact J → Convex ℝ J → (interior J).Nonempty →
      (volume J).toReal/Dh ≤ FinalRates.eta m →
      ∫⁻ x, (lattice x).hole J ∂measure ≤
        ENNReal.ofReal (Real.exp (-(volume J).toReal/Dh)+CR*Real.exp (-FinalRates.eta m))





def GaussianPositions (α β γ C₀ : ℝ) (n : ℕ) : Prop :=
  ∀ m D : ℕ, m+D=n → 0 < D → (D : ℝ) ≤ (n : ℝ)^α →
    ∀ K : Set (Fin (m+D) → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
        ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ (n : ℝ)^β →
          (1-C₀*(n : ℝ)^(-γ))*(volume (e '' K)).toReal*Folded.gamma y ≤
            (volume (coordinateFiber (e '' K) y)).toReal

end SingleLatticeCovering.Inputs

end
end

section

noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology


def sectionRadius (C : ℝ) (n : ℕ) : ℝ := (C+1)*((firstSize n : ℝ)+1)

lemma sectionRadius_pos {C : ℝ} (hC : 0 < C) (n : ℕ) : 0 < sectionRadius C n := by
  dsimp [sectionRadius]; positivity

lemma radius_sq_bound {C b r : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hr : r ≤ C*(b*Real.log (b+1)+1)) : r ≤ ((C+1)*(b+1))^2 := by
  have hl : Real.log (b+1) ≤ b := by simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < b+1)
  have hinner : b*Real.log (b+1)+1 ≤ (b+1)^2 := by nlinarith [mul_le_mul_of_nonneg_left hl hb]
  calc
    r ≤ C*(b*Real.log (b+1)+1) := hr
    _ ≤ C*(b+1)^2 := mul_le_mul_of_nonneg_left hinner hC
    _ ≤ (C+1)^2*(b+1)^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (sq_nonneg _)
    _ = _ := by ring

lemma eventually_first_polynomial {H r ε : ℝ} (hH : 0 < H) (hr : 0 < r) (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, H*((firstSize n : ℝ)+1)^k ≤ ε*(n : ℝ)^r := by
  filter_upwards [eventually_firstSize_le_log (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_bound k hr (div_pos hε hH)] with n hfirst hlog
  simp only [one_mul] at hfirst
  calc
    _ ≤ H*(Real.log (n : ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hfirst k) hH.le
    _ ≤ H*((ε/H)*(n : ℝ)^r) := mul_le_mul_of_nonneg_left hlog hH.le
    _ = _ := by field_simp




lemma eventually_marginal_scales {C α β γ C₀ : ℝ} (hC : 0 < C)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ 2 ≤ n-D ∧ (D : ℝ) ≤ (n : ℝ)^α ∧
      6*(D : ℝ)*sectionRadius C n < (n : ℝ)^β ∧
      C₀*(n : ℝ)^(-γ) ≤ 1/2 ∧
      sectionRadius C n^2/((n-D : ℕ) : ℝ)^2 ≤ 1 := by
  have _ := hC₀
  have herr : ∀ᶠ n : ℕ in atTop, C₀*(n : ℝ)^(-γ) ≤ 1/2 := by
    have ht : Tendsto (fun n : ℕ => C₀*(n : ℝ)^(-γ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop hγ).comp hn).const_mul C₀
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_first_polynomial hC hα (by norm_num : (0 : ℝ) < 1) 1,
    eventually_first_polynomial (show 0 < 6*C*(C+1) by positivity) hβ (by norm_num : (0 : ℝ) < 1/2) 2,
    eventually_first_polynomial (show 0 < C+1 by linarith) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2) 1,
    eventually_dimension_small hC,herr,eventually_ge_atTop (4 : ℕ)] with n hDim hRad hSmall hDsmall he hn D hD
  simp only [pow_one,one_mul] at hDim
  simp only [pow_one,Real.rpow_one] at hSmall
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdhalf := (hDsmall D hD).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hmhalf : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith
  have hm2 : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by linarith
  refine ⟨hDn,by exact_mod_cast hm2,hD.trans hDim,?_,he,?_⟩
  · have hDR : 6*(D : ℝ)*sectionRadius C n ≤ 6*C*(C+1)*((firstSize n : ℝ)+1)^2 := by
      dsimp [sectionRadius]
      have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ 6*((C+1)*((firstSize n : ℝ)+1)) by positivity)
      nlinarith
    have hp : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hn0 β
    exact hDR.trans_lt (hRad.trans_lt (by nlinarith))
  · have hRm : sectionRadius C n ≤ ((n-D : ℕ) : ℝ) := by
      dsimp [sectionRadius]
      linarith
    apply (div_le_one (sq_pos_of_pos (by linarith : (0 : ℝ) < ((n-D : ℕ) : ℝ)))).mpr
    exact pow_le_pow_left₀ (sectionRadius_pos hC n).le hRm 2


end SingleLatticeCovering.FinalRates

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal

lemma body_volume_pos {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < (volume K).toReal := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) hK.measure_ne_top
  exact (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma affine_body {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let he : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image he.continuous, hc.affine_image e.toAffineMap,?_⟩
  change (interior (he '' K)).Nonempty
  rw [←he.image_interior]
  exact hi.image he

lemma chain_first_le_dim {B : Block} (c : Chain B) : c.first.b ≤ c.dim := by
  induction c with
  | base B => rfl
  | append c B w ih => exact ih.trans (Nat.le_add_right _ _)


def coversAtBound (n : ℕ) (d : ℝ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
    ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ d






theorem eventual_main_reduction {α β γ C₀ CR : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) (hCR : 0 ≤ CR)
    (hGaussian : ∀ᶠ n : ℕ in atTop, GaussianPositions α β γ C₀ n)
    (hMean : ∀ m : ℕ, 2 ≤ m → ∀ Dh : ℝ, 0 < Dh → Nonempty (MeanHoleModel m Dh CR)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨cutoff,hcut,C,k,κ,hC,hk,hκ,hvertical⟩ := vertical_patterns_alphabets
  obtain ⟨Cstar,hstar,hconditions⟩ := FinalRates.final_conditions hC hk
    (show 0 < Real.exp (-1)/8 by positivity) (show 0 ≤ Real.exp 1/8 by positivity)
    hκ (show (1 : ℝ) ≤ 3 by norm_num) hCR
  refine ⟨Real.exp 1*Cstar,by positivity,?_⟩
  filter_upwards [hconditions,FinalRates.eventually_marginal_scales hC hα hβ hγ hC₀,
    FinalRates.firstSize_tendsto.eventually (eventually_ge_atTop cutoff), hGaussian]
      with n hn hscale hfirst hgaussian
  obtain ⟨B,c,hcb,hcs,hDim,hRad,hAlphabet,hPattern⟩ := hvertical (FinalRates.firstSize n) hfirst
  have hDdim : (c.fullDim : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) := by
    simpa [Chain.fullDim,Nat.cast_add] using hDim
  obtain ⟨hDn,hm,hcap,hload,hcrit,hcount⟩ := hn.2 c.fullDim hDdim
  obtain ⟨_,_,hDpower,hRadius,hErr,hSmall⟩ := hscale c.fullDim hDdim
  have hD : 0 < c.fullDim := by
    have hfirstdim := chain_first_le_dim c
    rw [hcb] at hfirstdim
    dsimp [Chain.fullDim]
    omega
  let m := n-c.fullDim
  have hmn : m+c.fullDim=n := Nat.sub_add_cancel hDn
  have hmnle : m ≤ n := Nat.sub_le _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let ρ := Cstar*(n : ℝ)*Real.log (n : ℝ)
  let ε := Real.exp (-k*(FinalRates.firstSize n : ℝ)^(70/100 : ℝ))
  let R := FinalRates.sectionRadius C n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2 :=
    FinalRates.radius_sq_bound hC.le (Nat.cast_nonneg _) hRad
  have step : coversAtBound (m+c.fullDim) ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ)) := by
    intro K hK hc hi
    obtain ⟨e,he⟩ := hgaussian m c.fullDim hmn hD hDpower K hK hc hi
    obtain ⟨heK,hec,hei⟩ := affine_body e hK hc hi
    have heV := body_volume_pos heK hei
    have hg : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
        (volume (e '' K)).toReal*gamma y/2 ≤ (volume (coordinateFiber (e '' K) y)).toReal := by
      intro y hy
      apply le_trans _ (he y (hy.trans hRadius.le))
      have hy0 : 0 < gamma y := Finset.prod_pos (fun j _ => gamma1_pos _)
      nlinarith [mul_nonneg (show 0 ≤ 1-C₀*(n : ℝ)^(-γ)-1/2 by linarith)
        (mul_nonneg heV.le hy0.le)]
    obtain ⟨model⟩ := hMean m hm ((volume (e '' K)).toReal/(ρ*c.det))
      (div_pos heV (mul_pos hρ c.det_pos))
    let := model.measurable
    let := model.probability
    obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := sections_and_mean_cover c hm hD (e '' K) heK hec heV
      (FinalRates.sectionRadius_pos hC n) hrad hSmall hg κ ρ ε (Real.sqrt (m : ℝ))
      (8*(n : ℝ)*Real.log (n : ℝ)) CR hρ (Real.sqrt_nonneg _) (by positivity) hCR
      (by
        intro y
        obtain ⟨P,hPn,hPb,hPl,hPt,hPw⟩ := hPattern y
        exact ⟨P,hPn,hPb,hPl,hPw⟩)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hload) hcap hcrit (by
        intro δ s hs
        have hs' : (s.card : ℝ) ≤ (3*(n : ℝ)^2)^c.fullDim := hs.trans (by
          gcongr)
        have ha : ∀ j < c.fullDim, Real.log ((c.alphabetSeq j).card+1 : ℝ) ≤
            Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2 := by
          intro j hj
          simpa only [c.alphabetSeq_fin ⟨j,hj⟩] using hAlphabet ⟨j,hj⟩
        simpa only [Nat.sub_add_cancel hDn] using hcount s c.alphabetSeq hs' ha)
      model.measure model.lattice model.covolume model.measurable_hole model.mean
    let := hd
    let := hfull
    have hb : (volume (e '' K)).toReal/ZLattice.covolume Λ volume ≤
        (Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by
      convert hbound using 1 ; dsimp [ρ] ; ring
    exact pull_back_cover e K Λ hcover hb
  change coversAtBound n ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ))
  simpa only [hmn] using step


end SingleLatticeCovering.Assembly

end
end

section

noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise
namespace SingleLatticeCovering.FiniteDimensions




theorem maximal_basis {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (h0 : (0 : Fin n → ℝ) ∈ interior K) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ),
      (∀ j, b j ∈ K) ∧ ∀ x ∈ K, ∀ j, |b.repr x j| ≤ 1 := by
  classical
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let v₀ : Fin n → (Fin n → ℝ) := fun j => (r/2) • Pi.single j (1 : ℝ)
  have hv₀ : ∀ j, v₀ j ∈ K := by
    intro j
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    simp only [v₀,norm_smul,Pi.norm_single,Real.norm_eq_abs,abs_one,mul_one,
      abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hdet₀ : (Matrix.of v₀).det = (r/2)^n := by
    have he : Matrix.of v₀ = (r/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [v₀,Pi.single_apply,Matrix.one_apply,Pi.smul_apply,eq_comm]
    rw [he,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]
  have hS : IsCompact {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  have hcont : Continuous (fun v : Fin n → (Fin n → ℝ) => |(Matrix.of v).det|) := by
    fun_prop
  obtain ⟨v,hv,hmax⟩ := hS.exists_isMaxOn ⟨v₀,hv₀⟩ hcont.continuousOn
  have hdet : (Matrix.of v).det ≠ 0 := by
    have h : |(Matrix.of v₀).det| ≤ |(Matrix.of v).det| := hmax hv₀
    rw [hdet₀,abs_of_pos (pow_pos (by positivity : 0 < r/2) _)] at h
    intro hz
    rw [hz,abs_zero] at h
    exact (not_le_of_gt (pow_pos (by positivity : 0 < r/2) _)) h
  let b := basisOfLinearIndependentOfCardEqFinrank' v
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet) (by simp)
  have hb : (b : Fin n → (Fin n → ℝ)) = v := by
    simp [b]
  refine ⟨b,?_,?_⟩
  · intro j
    rw [show b j=v j from congrFun hb j]
    exact hv j
  · intro x hx j
    have hupdate : (Function.update v j x) ∈ {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} := by
      intro k
      by_cases hk : k=j
      · subst k; simpa using hx
      · simpa [hk] using hv k
    have hbound := hmax hupdate
    have hd : (Matrix.of (Function.update v j x)).det = b.repr x j*(Matrix.of v).det := by
      have hs := b.sum_repr x
      have ht := Matrix.det_updateRow_sum (Matrix.of b) j (fun k => b.repr x k)
      change (Matrix.of (Function.update (fun k => b k) j (∑ k, b.repr x k • b k))).det =
        b.repr x j*(Matrix.of b).det at ht
      rw [hs,hb] at ht
      exact ht
    change |(Matrix.of (Function.update v j x)).det| ≤ |(Matrix.of v).det| at hbound
    rw [hd,abs_mul] at hbound
    exact (mul_le_mul_iff_left₀ (abs_pos.mpr hdet)).mp (by simpa [mul_comm] using hbound)


end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise

lemma convex_basis_cube {n : ℕ} (hn : 0 < n) (K : Set (Fin n → ℝ))
    (hconv : Convex ℝ K) (h0 : (0 : Fin n → ℝ) ∈ K)
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (hb : ∀ j, b j ∈ K) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ b.equivFun.symm ⁻¹' K := by
  intro x hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j, x j ≤ 1 := calc
    ∑ j, x j ≤ ∑ _j : Fin n, 1/(n : ℝ) := Finset.sum_le_sum (fun j _ => hx.2 j)
    _ = 1 := by simp [hnr.ne']
  let w : Fin (n+1) → ℝ := Fin.cons (1-∑ j, x j) x
  let z : Fin (n+1) → (Fin n → ℝ) := Fin.cons 0 b
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), 0 ≤ w j := by
    intro j _
    refine Fin.cases ?_ (fun i => ?_) j
    · exact sub_nonneg.mpr hsum
    · exact hx.1 i
  have hw1 : ∑ j, w j = 1 := by simp [w,Fin.sum_univ_succ]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), z j ∈ K := by
    intro j _
    exact Fin.cases h0 hb j
  have hc := hconv.sum_mem hw hw1 hz
  change b.equivFun.symm x ∈ K
  rw [Basis.equivFun_symm_apply]
  simpa only [Fin.sum_univ_succ,w,z,Fin.cons_zero,Fin.cons_succ,smul_zero,zero_add] using hc

lemma integer_cube_cover {n : ℕ} (hn : 0 < n) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ))+
      (contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') : Set (Fin n → ℝ)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let l : Fin n → ℝ := fun j => (⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)
  let q : Fin n → ℝ := fun j => Int.fract ((n : ℝ)*x j)/(n : ℝ)
  have hl : l ∈ contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') := by
    rw [mem_contractLattice]
    convert integer_mem n (fun j => ⌊(n : ℝ)*x j⌋) using 1
    ext j
    simp only [Pi.smul_apply,smul_eq_mul,l]
    field_simp
  refine ⟨q,⟨?_,?_⟩,l,hl,?_⟩
  · intro j
    exact div_nonneg (Int.fract_nonneg _) hnr.le
  · intro j
    exact (div_le_div_iff_of_pos_right hnr).mpr (Int.fract_lt_one _).le
  · ext j
    change Int.fract ((n : ℝ)*x j)/(n : ℝ)+(⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)=x j
    rw [←add_div,Int.fract_add_floor]
    exact mul_div_cancel_left₀ _ hnr.ne'



end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise



theorem finite_dimension_cover {n : ℕ} (hn : 0 < n)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
      IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=univ ∧
      (volume K).toReal / ZLattice.covolume L ≤ (2*(n : ℝ))^n := by
  classical
  obtain ⟨x₀,hx₀⟩ := hinterior
  let t := Homeomorph.addRight x₀
  let K₀ := t ⁻¹' K
  have hK₀ : IsCompact K₀ := t.isCompact_preimage.mpr hK
  have h0 : (0 : Fin n → ℝ) ∈ interior K₀ := by
    rw [←t.preimage_interior]
    change 0+x₀ ∈ interior K
    simpa using hx₀
  have hconv₀ : Convex ℝ K₀ := by
    intro x hx y hy a b ha hb hab
    have hh := hconv hx hy ha hb hab
    change a • (x+x₀)+b • (y+x₀) ∈ K at hh
    change a • x+b • y+x₀ ∈ K
    have he : a • (x+x₀)+b • (y+x₀) = a • x+b • y+x₀ := by
      calc
        _ = (a • x+b • y)+(a+b) • x₀ := by module
        _ = _ := by rw [hab,one_smul]
    rwa [he] at hh
  obtain ⟨b,hb,hbound⟩ := maximal_basis K₀ hK₀ h0
  let e := b.equivFun.symm
  let K' := e ⁻¹' K₀
  have hsmall : Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ K' :=
    convex_basis_cube hn K₀ hconv₀ (interior_subset h0) b hb
  have hlarge : K' ⊆ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := by
    intro x hx
    have hb' := hbound (e x) hx
    have hj (j : Fin n) : |x j| ≤ 1 := by
      have hh : |b.equivFun (e x) j| ≤ 1 := hb' j
      simpa only [e,LinearEquiv.apply_symm_apply] using hh
    exact ⟨fun j => (abs_le.mp (hj j)).1,fun j => (abs_le.mp (hj j)).2⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let L₀ := contractLattice (integerLattice n) (n : ℝ) hnr.ne'
  have hcover : K'+(L₀ : Set (Fin n → ℝ))=univ := by
    apply Set.eq_univ_of_univ_subset
    rw [←integer_cube_cover hn]
    exact Set.add_subset_add_right hsmall
  have hvolume : (volume K').toReal ≤ (2 : ℝ)^n := by
    have hh := ENNReal.toReal_mono (isCompact_Icc.measure_ne_top (μ := volume)) (measure_mono hlarge)
    rw [Real.volume_Icc_pi_toReal (by intro j; norm_num)] at hh
    norm_num at hh
    exact hh
  have hcov : ZLattice.covolume L₀ = (n : ℝ)⁻¹^n := by
    rw [contractLattice_covolume _ _ hnr,integerLattice_covolume,mul_one]
  have hdens : (volume K').toReal / ZLattice.covolume L₀ ≤ (2*(n : ℝ))^n := by
    rw [hcov,inv_pow,div_inv_eq_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right hvolume (pow_nonneg hnr.le _)
  have himage : (fun x => e x+x₀) '' K'=K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm (x-x₀),?_,?_⟩
      · change e (e.symm (x-x₀))+x₀ ∈ K
        simpa using hx
      · simp
  refine ⟨image L₀ e,inferInstance,inferInstance,?_,?_⟩
  · rw [←himage]
    exact affine_image_cover L₀ e x₀ K' hcover
  · rw [←himage,affine_image_density]
    exact hdens


end SingleLatticeCovering.FiniteDimensions


end
end
end

end OAI
