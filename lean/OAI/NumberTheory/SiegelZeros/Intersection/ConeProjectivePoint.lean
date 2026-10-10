import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.GenericNormalization
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLaurent
import OAI.NumberTheory.SiegelZeros.Structure.ConeMapEval

namespace OAI

namespace SiegelZeros

section
section
section
namespace WeightedTorusJets.Geometry

theorem torus_chart_prime_height_add_quotient_dim {K : Type*} [Field K] (n : ℕ)
    (p : Ideal (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))) [p.IsPrime] :
    (p.height : WithBot ℕ∞) +
      ringKrullDim (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ p) = n := by
  let R := MvPolynomial (Fin n) K
  let t : R := ∏ i : Fin n, MvPolynomial.X i
  let T := Localization.Away t
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  simpa only [torus_chart_ringKrullDim] using
    prime_height_add_quotient_dim_eq_of_finiteType (K := K) p

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

theorem finiteType_prime_codimension_nat
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : Ideal A) [p.IsPrime] (n : ℕ)
    (hn : ringKrullDim A = n) :
    ∃ d : ℕ, d ≤ n ∧ ringKrullDim (A ⧸ p) = d ∧ p.height = (n - d : ℕ) := by
  obtain ⟨d, hd, _⟩ := finiteType_dimension_trdeg (K := K) (A := A ⧸ p)
  have hp_le : p.height ≤ n := by
    have hpdim := p.height_le_ringKrullDim_of_isPrime
    rw [hn] at hpdim
    exact_mod_cast hpdim
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp
    (lt_of_le_of_lt hp_le (ENat.natCast_lt_top n)).ne
  have heq := prime_height_add_quotient_dim_eq_of_finiteType (K := K) p
  rw [← hh, hd, hn] at heq
  have hsum : h + d = n := by exact_mod_cast heq
  refine ⟨d, ?_, hd, ?_⟩
  · exact hsum ▸ Nat.le_add_left d h
  · rw [← hh, ← hsum, Nat.add_sub_cancel]

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem mul_X_none_pow_mem_coneIdeal_iff (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) (n : ℕ) :
    f * X none ^ n ∈ coneIdeal p ↔ f ∈ coneIdeal p := by
  change coneMap p (f * X none ^ n) = 0 ↔ coneMap p f = 0
  rw [map_mul, map_pow, coneMap_X_none]
  exact ⟨Polynomial.mul_X_pow_eq_zero, fun h => by rw [h, zero_mul]⟩

theorem coneMap_of_isHomogeneous (p : Ideal (MvPolynomial σ K))
    {f : MvPolynomial (Option σ) K} {n : ℕ} (hf : f.IsHomogeneous n) :
    coneMap p f = Polynomial.C (Ideal.Quotient.mk p (coneDehomogenize f)) *
      Polynomial.X ^ n := by
  have heq := coneMap_homogeneousComponent p f n
  rw [homogeneousComponent_eq_self hf] at heq
  have heval : (coneMap p f).coeff n = Ideal.Quotient.mk p (coneDehomogenize f) := by
    rw [← eval_one_coneMap, heq]
    simp
  rwa [heval] at heq

theorem homogeneous_mem_coneIdeal_iff (p : Ideal (MvPolynomial σ K))
    {f : MvPolynomial (Option σ) K} {n : ℕ} (hf : f.IsHomogeneous n) :
    f ∈ coneIdeal p ↔ coneDehomogenize f ∈ p := by
  change coneMap p f = 0 ↔ coneDehomogenize f ∈ p
  rw [coneMap_of_isHomogeneous p hf]
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact Polynomial.C_injective (by simpa only [map_zero] using Polynomial.mul_X_pow_eq_zero h)
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_mul]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_ideal_le_coneIdeal_iff (p : Ideal (MvPolynomial σ K))
    (J : Ideal (MvPolynomial (Option σ) K))
    (hJ : J.IsHomogeneous (homogeneousSubmodule (Option σ) K)) :
    J ≤ coneIdeal p ↔ Ideal.map coneDehomogenize.toRingHom J ≤ p := by
  constructor
  · intro h
    exact (Ideal.map_mono h).trans (map_coneIdeal_dehomogenize_le p)
  · intro h f hf
    apply (MvPolynomial.mem_iff_homogeneousComponent_mem (coneIdeal_isHomogeneous p) f).mpr
    intro n
    apply (homogeneous_mem_coneIdeal_iff p (homogeneousComponent_isHomogeneous n f)).mpr
    exact h (Ideal.mem_map_of_mem _ (homogeneousComponent_mem_of_mem hJ hf n))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coneIdeal_eq_homogeneousCore (p : Ideal (MvPolynomial σ K)) :
    coneIdeal p =
      ((Ideal.comap coneDehomogenize.toRingHom p).homogeneousCore
        (homogeneousSubmodule (Option σ) K)).toIdeal := by
  apply le_antisymm
  · have hle : coneIdeal p ≤ Ideal.comap coneDehomogenize.toRingHom p :=
      Ideal.map_le_iff_le_comap.mp (map_coneIdeal_dehomogenize_le p)
    have hmono := Ideal.homogeneousCore_mono (homogeneousSubmodule (Option σ) K) hle
    have heq := (coneIdeal_isHomogeneous p).toIdeal_homogeneousCore_eq_self
    rw [← heq]
    exact hmono
  · apply (homogeneous_ideal_le_coneIdeal_iff p _
      (HomogeneousIdeal.isHomogeneous _)).mpr
    apply Ideal.map_le_iff_le_comap.mpr
    exact Ideal.toIdeal_homogeneousCore_le _ _

noncomputable def coneProjectivePoint (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ProjectiveSpectrum (homogeneousSubmodule (Option σ) K) where
  asHomogeneousIdeal := ⟨coneIdeal p, coneIdeal_isHomogeneous p⟩
  isPrime := coneIdeal_isPrime p
  not_irrelevant_le := by
    intro h
    apply X_none_not_mem_coneIdeal p
    exact h (HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Option σ) K) (by decide : 0 < (1 : ℕ))
      (isHomogeneous_X K none))

theorem coneProjectivePoint_mem_basicOpen (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    coneProjectivePoint p ∈ ProjectiveSpectrum.basicOpen
      (homogeneousSubmodule (Option σ) K) (X none) := by
  exact X_none_not_mem_coneIdeal p

theorem coneIdeal_le_iff (p q : Ideal (MvPolynomial σ K)) :
    coneIdeal p ≤ coneIdeal q ↔ p ≤ q := by
  rw [homogeneous_ideal_le_coneIdeal_iff q _ (coneIdeal_isHomogeneous p),
    map_coneIdeal_dehomogenize]

theorem closure_coneProjectivePoint (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    closure ({coneProjectivePoint p} :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) K) (coneIdeal p) := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  rfl

theorem coneProjectivePoint_mem_closure_iff (p q : Ideal (MvPolynomial σ K))
    [p.IsPrime] [q.IsPrime] :
    coneProjectivePoint q ∈ closure ({coneProjectivePoint p} :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))) ↔ p ≤ q := by
  rw [← ProjectiveSpectrum.le_iff_mem_closure]
  exact coneIdeal_le_iff p q

end WeightedTorusJets.Geometry

noncomputable section
open MvPolynomial HomogeneousLocalization

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k ι : Type u) [CommRing k]

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem affineProj_homogenizing_mem (k ι : Type u) [CommRing k] :
    (X (none : Option ι) : MvPolynomial (Option ι) k) ∈
      homogeneousSubmodule (Option ι) k 1 := isHomogeneous_X k (none : Option ι)

end WeightedTorusJets.Geometry
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

universe uChart

theorem basicOpenToSpec_coneProjectivePoint
    {K σ : Type uChart} [CommRing K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Proj.basicOpenToSpec (homogeneousSubmodule (Option σ) K) (X (none : Option σ))
      ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩ =
        PrimeSpectrum.comap (affineProjChartMap (k := K) (fun i : σ => X i))
          ⟨p, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Option σ) K)
    (isHomogeneous_X K (none : Option σ)) z
  change HomogeneousLocalization.mk _ ∈
    ((ProjectiveSpectrum.Proj.toSpec (homogeneousSubmodule (Option σ) K)
      (X (none : Option σ))).base
        ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩).asIdeal ↔ _
  refine (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
    (homogeneousSubmodule (Option σ) K)
    ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩ _).trans ?_
  change a ∈ coneIdeal p ↔ affineProjChartMap (k := K) (fun i : σ => X i)
    (Away.mk (homogeneousSubmodule (Option σ) K) (isHomogeneous_X K (none : Option σ)) n a ha) ∈ p
  rw [affineProjChartMap_mk]
  have heval : affineProjEval (k := K) (fun i : σ => X i) =
      (coneDehomogenize : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K) := by
    ext i
    cases i <;> simp [affineProjEval, coneDehomogenize]
  rw [heval]
  exact homogeneous_mem_coneIdeal_iff p ha

theorem affineIntoProj_polynomial_point
    {K σ : Type uChart} [CommRing K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (affineIntoProj (k := K) (fun i : σ => X i)) ⟨p, inferInstance⟩ =
      coneProjectivePoint p := by
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule (Option σ) K)
    (X (none : Option σ)) (affineProj_homogenizing_mem K σ) (by decide)
  change (Proj.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ))).ι
    (e.inv (PrimeSpectrum.comap (affineProjChartMap (k := K) (fun i : σ => X i))
      ⟨p, inferInstance⟩)) = _
  rw [← basicOpenToSpec_coneProjectivePoint p]
  change (Proj.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ))).ι
    (e.inv (e.hom ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩)) = _
  exact congrArg
    (fun f : (Proj.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ))).toScheme ⟶
        (Proj.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ))).toScheme =>
      (Proj.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ))).ι
        (f ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩)) e.hom_inv_id

theorem closure_affineIntoProj_zeroLocus
    {K σ : Type uChart} [CommRing K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    closure ((affineIntoProj (k := K) (fun i : σ => X i)) ''
      PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K))) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) K) (coneIdeal p) := by
  rw [← PrimeSpectrum.closure_singleton (⟨p, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ K))]
  have hc : Continuous (fun x : PrimeSpectrum (MvPolynomial σ K) =>
      ((affineIntoProj (k := K) (fun i : σ => X i)) x :
        ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))) :=
    (affineIntoProj (k := K) (fun i : σ => X i)).continuous
  refine (closure_image_closure hc).trans ?_
  rw [Set.image_singleton]
  exact (congrArg (fun x : ProjectiveSpectrum (homogeneousSubmodule (Option σ) K) =>
    closure ({x} : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))))
      (affineIntoProj_polynomial_point p)).trans (closure_coneProjectivePoint p)

end WeightedTorusJets.Geometry

end
end

section
namespace WeightedTorusJets.Geometry

theorem coneIdeal_quotient_ringKrullDim {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ringKrullDim (MvPolynomial (Option σ) K ⧸ coneIdeal p) =
      ringKrullDim (MvPolynomial σ K ⧸ p) + 1 := by
  let : (coneIdeal p).IsPrime := coneIdeal_isPrime p
  obtain ⟨d, hdle, hd, hheight⟩ := finiteType_prime_codimension_nat (K := K) p (Nat.card σ)
    (by simp)
  obtain ⟨c, hc, _⟩ := finiteType_dimension_trdeg (K := K)
    (A := MvPolynomial (Option σ) K ⧸ coneIdeal p)
  have hcone := prime_height_add_quotient_dim_eq_of_finiteType (K := K) (coneIdeal p)
  rw [coneIdeal_height, hheight, hc] at hcone
  have heq : (Nat.card σ - d) + c = Nat.card σ + 1 := by
    have : ringKrullDim (MvPolynomial (Option σ) K) =
        (Nat.card σ + 1 : ℕ) := by simp
    rw [this] at hcone
    exact_mod_cast hcone
  have hcd : c = d + 1 := by omega
  rw [hc, hd, hcd]
  simp

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem projective_zeroLocus_topologicalKrullDim_eq_order (I : Ideal A) :
    topologicalKrullDim (ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A)) =
      Order.krullDim (ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A)) := by
  let : QuasiSober (ProjectiveSpectrum 𝒜) := inferInstanceAs (QuasiSober (Proj 𝒜))
  let : T0Space (ProjectiveSpectrum 𝒜) := inferInstanceAs (T0Space (Proj 𝒜))
  let Z := ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A)
  have : QuasiSober Z := (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 (I : Set A)).isClosedEmbedding_subtypeVal.quasiSober
  have hs (p q : ProjectiveSpectrum 𝒜) : p ≤ q ↔ p ⤳ q :=
    (ProjectiveSpectrum.le_iff_mem_closure 𝒜 p q).trans specializes_iff_mem_closure.symm
  let e : Z ≃o (TopologicalSpace.IrreducibleCloseds Z)ᵒᵈ :=
    { __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
      map_rel_iff' {p q} :=
        (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
          ((subtype_specializes_iff p q).trans (hs p.1 q.1).symm) }
  exact Order.krullDim_orderDual.symm.trans (Order.krullDim_eq_of_orderIso e).symm

theorem projective_zeroLocus_dim_le_of_cone_dim
    (I m : Ideal A) [m.IsPrime]
    (hm : ∀ x : ProjectiveSpectrum 𝒜, x.asHomogeneousIdeal.toIdeal < m)
    (n : ℕ) (hdim : ringKrullDim (A ⧸ I) ≤ n + 1) :
    topologicalKrullDim (ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A)) ≤ n := by
  rw [projective_zeroLocus_topologicalKrullDim_eq_order]
  apply iSup_le
  intro l
  let e : ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A) ↪o PrimeSpectrum.zeroLocus (I : Set A) :=
    OrderEmbedding.ofMapLEIff
      (fun x ↦ ⟨⟨x.1.asHomogeneousIdeal.toIdeal, x.1.isPrime⟩, x.2⟩)
      (fun _ _ ↦ Iff.rfl)
  let q := l.map e e.strictMono
  let m' : PrimeSpectrum.zeroLocus (I : Set A) :=
    ⟨⟨m, inferInstance⟩, l.last.2.trans (hm l.last.1).le⟩
  have hlt : q.last < m' := hm l.last.1
  have hlength := Order.LTSeries.length_le_krullDim (q.snoc m' hlt)
  rw [← ringKrullDim_quotient] at hlength
  have hle : (l.length + 1 : ℕ) ≤ n + 1 := by
    have hh := hlength.trans hdim
    change ((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ n + 1 at hh
    exact_mod_cast hh
  exact_mod_cast Nat.le_of_succ_le_succ hle

end WeightedTorusJets.Geometry

end

end
end

end SiegelZeros

end OAI
