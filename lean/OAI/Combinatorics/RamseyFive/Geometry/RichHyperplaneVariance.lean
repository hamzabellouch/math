import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q
import OAI.Combinatorics.RamseyFive.Geometry.ExceptionalCenters

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem rich_hyperplane_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (X : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) (M : ℕ)
    (hM : ∀ b ∈ B, M ≤ (X.filter fun x => Incident x b).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (B.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let w (x : ℙ K V) : ℝ := if x ∈ X then 1 else 0
  have hw : ∑ x, w x = (X.card:ℝ) := by simp [w]
  have hw2 : ∑ x, w x^2 = (X.card:ℝ) := by simp [w]
  have hweight (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ((X.filter fun x => Incident x b).card:ℝ) := by
    simp [weightOnHyperplane, incidenceEntry, w, mul_ite]
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card
  have hvariance := incidence_variance hdim hd w
  rw [hw,hw2] at hvariance
  have hrow (b : ℙ K (Module.Dual K V)) (hb : b ∈ B) :
      (M:ℝ)^2 ≤ 4*(weightOnHyperplane w b-μ)^2 := by
    have hm : (M:ℝ) ≤ weightOnHyperplane w b := by rw [hweight]; exact_mod_cast hM b hb
    have hmean' : 2*μ ≤ M := by dsimp [μ]; nlinarith [hmean]
    have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hle : 0 ≤ 2*(weightOnHyperplane w b-μ)-(M:ℝ) := by linarith
    have hge : 0 ≤ 2*(weightOnHyperplane w b-μ)+(M:ℝ) := by linarith
    nlinarith [mul_nonneg hle hge]
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hsub := Finset.sum_le_univ_sum_of_nonneg (s := B)
    (fun b => sq_nonneg (weightOnHyperplane w b-μ))
  have hvar : ∑ b, (weightOnHyperplane w b-μ)^2 ≤ (Nat.card K:ℝ)^(d-1)*X.card := hvariance
  linarith

theorem rich_subspaces_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (F.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let b (A : F) : ℙ K (Module.Dual K V) := dualOfHyperplane hdim A.val (hF A.val A.property)
  let B := F.attach.image b
  have hi : Function.Injective b := by
    intro A B hAB
    apply Subtype.ext
    have h := congrArg (fun c : ℙ K (Module.Dual K V) => LinearMap.ker c.rep) hAB
    simpa only [b,ker_dualOfHyperplane] using h
  have hBc : B.card = F.card := by simp [B,Finset.card_image_of_injective _ hi]
  have hrich (c : ℙ K (Module.Dual K V)) (hc : c ∈ B) :
      M ≤ (X.filter fun x => Incident x c).card := by
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Incident,b,ker_dualOfHyperplane] using hM A.val A.property
  have h := rich_hyperplane_variance hdim hd X B M hrich hmean
  simpa only [hBc] using h

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    Finset (ℙ K H) :=
  (X.subtype (fun p => p.submodule ≤ H)).map (subspacePointsEquiv H).symm.toEmbedding

lemma card_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    (pointsInSubspace H X).card = (X.filter fun p => p.submodule ≤ H).card := by
  simp [pointsInSubspace]

lemma mem_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) (p : ℙ K H) :
    p ∈ pointsInSubspace H X ↔ ((subspacePointsEquiv H) p).val ∈ X := by
  simp [pointsInSubspace]

lemma subspacePointsEquiv_submodule (H A : Submodule K V) (p : ℙ K H) :
    p.submodule ≤ A.comap H.subtype ↔ ((subspacePointsEquiv H) p).val.submodule ≤ A := by
  induction p using Projectivization.ind with | h v hv =>
  change (Projectivization.mk K v hv).submodule ≤ A.comap H.subtype ↔
    (Projectivization.map H.subtype H.injective_subtype (Projectivization.mk K v hv)).submodule ≤ A
  rw [Projectivization.map_mk, Projectivization.submodule_mk,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma card_pointsInSubspace_filter (H A : Submodule K V) (hAH : A ≤ H)
    (X : Finset (ℙ K V)) :
    ((pointsInSubspace H X).filter fun p => p.submodule ≤ A.comap H.subtype).card =
      (X.filter fun p => p.submodule ≤ A).card := by
  apply Finset.card_bij (fun p _ => ((subspacePointsEquiv H) p).val)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(mem_pointsInSubspace H X p).mp hpX,
      (subspacePointsEquiv_submodule H A p).mp hpA⟩
  · intro p hp q hq hpq
    exact (subspacePointsEquiv H).injective (Subtype.ext hpq)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    let z : {p : ℙ K V // p.submodule ≤ H} := ⟨p,hpA.trans hAH⟩
    refine ⟨(subspacePointsEquiv H).symm z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [mem_pointsInSubspace, Equiv.apply_symm_apply]
        exact hpX
      · rw [subspacePointsEquiv_submodule, Equiv.apply_symm_apply]
        exact hpA
    · simp [z]

lemma comap_subtype_finrank [FiniteDimensional K V] (H A : Submodule K V) (hAH : A ≤ H) :
    finrank K (A.comap H.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq H, Submodule.map_comap_subtype, inf_eq_right.mpr hAH]

lemma comap_subtype_injOn (H : Submodule K V) :
    Set.InjOn (fun A : Submodule K V => A.comap H.subtype) {A | A ≤ H} := by
  intro A hA B hB hAB
  change A ≤ H at hA
  change B ≤ H at hB
  have he := congrArg (fun W : Submodule K H => W.map H.subtype) hAB
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hA, inf_eq_right.mpr hB] using he

theorem rich_hyperplanes_inside_subspace [FiniteDimensional K V] [Finite K]
    {d : ℕ} (hd : 1 ≤ d) (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(X.filter fun p => p.submodule ≤ H).card := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hm (A : Submodule K H) (hA : A ∈ FH) :
      M ≤ ((pointsInSubspace H X).filter fun p => p.submodule ≤ A).card := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [card_pointsInSubspace_filter H B (Finset.mem_filter.mp hB).2]
    exact hM B (Finset.mem_filter.mp hB).1
  have hμ : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(pointsInSubspace H X).card ≤ M := by
    simpa only [card_pointsInSubspace] using hmean
  have hh := rich_subspaces_variance hH hd FH hdimF (pointsInSubspace H X) M hm hμ
  simpa only [hc, card_pointsInSubspace] using hh

theorem rich_planes_inside_hyperplane [FiniteDimensional K V] [Finite K]
    (H : Submodule K V) (hH : finrank K H = 4)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^2*(X.filter fun p => p.submodule ≤ H).card := by
  exact rich_hyperplanes_inside_subspace (by omega : 1 ≤ (3:ℕ)) H hH F hF X M hM hmean

end SharpRamseyFive.RichPlaneGeometry

end OAI
