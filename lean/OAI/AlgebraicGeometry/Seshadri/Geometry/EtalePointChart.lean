import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.GeneratedEtaleCoordinates
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SheafExactness
import OAI.AlgebraicGeometry.Seshadri.Jets.PolynomialJets

namespace OAI


                                         
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

lemma etale_aeval_reindex {ι κ : Type} (x : ι → S) (h : (aeval (R := K) x).toRingHom.Etale)
    (e : κ ≃ ι) : (aeval (R := K) (fun i => x (e i))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (renameEquiv K e).toRingEquiv h
  convert he using 1
  apply RingHom.ext
  intro p
  change aeval (fun i => x (e i)) p = aeval x (rename e p)
  exact (aeval_rename e x p).symm

lemma etale_aeval_center {ι : Type} (x : ι → S)
    (h : (aeval (R := K) x).toRingHom.Etale) (ρ : S →ₐ[K] K) :
    (aeval (R := K) (fun i => x i - algebraMap K S (ρ (x i)))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (polynomialTranslate (fun i => ρ (x i))).symm.toRingEquiv h
  convert he using 1
  apply ringHom_ext
  · intro c; simp [polynomialTranslate]
  · intro i; simp [polynomialTranslate]

theorem exists_centered_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ x : Fin n → S, (∀ i, ρ (x i) = 0) ∧
      (aeval (R := K) x).toRingHom.Etale := by
  obtain ⟨κ, hκ, x, hcard, hx⟩ := exists_etale_coordinates (R := K) (S := S) n
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hcard)
  let y := fun i : Fin n => x (e.symm i)
  refine ⟨fun i => y i - algebraMap K S (ρ (y i)), ?_,
    etale_aeval_center y (etale_aeval_reindex x hx e.symm) ρ⟩
  intro i
  simp

end

noncomputable section
variable {R : Type*} [CommRing R]

lemma exists_away_map_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) ≤
      J.map (algebraMap R (Localization.Away s)) := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hden : ∀ x : t, ∃ s : p.primeCompl, s.val * x.val ∈ J := by
    intro x
    have hx : algebraMap R (Localization.AtPrime p) x.val ∈
        J.map (algebraMap R (Localization.AtPrime p)) :=
      hle (Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span x.property))
    obtain ⟨s, hs, h⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ J x.val).mp hx
    exact ⟨⟨s, hs⟩, h⟩
  choose d hd using hden
  let s : p.primeCompl := ∏ x : t, d x
  refine ⟨s.val, s.property, Ideal.map_le_iff_le_comap.mpr ?_⟩
  rw [← ht, Ideal.span_le]
  intro x hx
  have hdiv : d ⟨x, hx⟩ ∣ s := Finset.dvd_prod_of_mem d (Finset.mem_univ _)
  obtain ⟨c, hc⟩ := hdiv
  have hmul : s.val * x ∈ J := by
    have h := J.mul_mem_left c.val (hd ⟨x, hx⟩)
    simpa only [hc, Submonoid.coe_mul, mul_assoc, mul_left_comm] using h
  change algebraMap R (Localization.Away s.val) x ∈
    J.map (algebraMap R (Localization.Away s.val))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s.val) _ J x).mpr
  exact ⟨s.val, Submonoid.mem_powers _, hmul⟩

lemma exists_away_map_eq_of_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hJI : J ≤ I)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hs, hle⟩ := exists_away_map_le I J p hI heq.le
  exact ⟨s, hs, le_antisymm hle (Ideal.map_mono hJI)⟩

end

noncomputable section
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma unramified_map_under_local [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] (q : Ideal S) [q.IsPrime] :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      q.map (algebraMap S (Localization.AtPrime q)) := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have hmax : (maximalIdeal Rp).map (algebraMap Rp Sq) = maximalIdeal Sq :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal q Sq] at hmax
  exact hmax

theorem exists_unramified_fiber_neighborhood [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (q : Ideal S) [q.IsPrime] :
    ∃ s : S, s ∉ q ∧ q.map (algebraMap S (Localization.Away s)) =
      ((q.under R).map (algebraMap R S)).map
        (algebraMap S (Localization.Away s)) := by
  apply exists_away_map_eq_of_le q ((q.under R).map (algebraMap R S)) q
    (Ideal.fg_of_isNoetherianRing q) Ideal.map_comap_le
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact (unramified_map_under_local (R := R) q).symm

end

noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem exists_centered_etale_point_chart (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ (x : Fin n → S) (s : S), ρ s ≠ 0 ∧ (∀ i, ρ (x i) = 0) ∧
      ((algebraMap S (Localization.Away s)).comp (aeval (R := K) x).toRingHom).Etale ∧
      (RingHom.ker ρ).map (algebraMap S (Localization.Away s)) =
        (idealOfVars (Fin n) K).map
          ((algebraMap S (Localization.Away s)).comp (aeval (R := K) x).toRingHom) := by
  obtain ⟨x, hx, he⟩ := exists_centered_etale_coordinates n ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin n) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin n) K) S := he
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := K) (S := S)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let q := RingHom.ker ρ
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
    (fun c => ⟨algebraMap K S c, by simp⟩)
  have hp : q.under (MvPolynomial (Fin n) K) = idealOfVars (Fin n) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  obtain ⟨s, hs, hI⟩ :=
    exists_unramified_fiber_neighborhood (R := MvPolynomial (Fin n) K) q
  refine ⟨x, s, hs, hx, ?_, ?_⟩
  · change (algebraMap (MvPolynomial (Fin n) K) (Localization.Away s)).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  · rw [hp, Ideal.map_map] at hI
    convert hI using 1

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.AlgebraicJets
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

end
end MaximalSeshadri.PointBlowup

end


end OAI
