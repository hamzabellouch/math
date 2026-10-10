import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceQuadraticEuler

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := schemeHasExt

lemma cohomologyDimension_iso (p : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    cohomologyDimension p M n = cohomologyDimension p N n := by
  let := Module.compHom (cohomology M n) (baseScalars p)
  let := Module.compHom (cohomology N n) (baseScalars p)
  exact (cohomologyIso p e n).finrank_eq

theorem cohomologyDimension_le_of_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ))
    {T : ShortComplex X.Modules} (hT : T.ShortExact) (n : ℕ)
    (hf : letI := Module.compHom (cohomology T.X₁ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₁ n))
    [Subsingleton (cohomology T.X₃ n)] :
    cohomologyDimension p T.X₂ n ≤ cohomologyDimension p T.X₁ n := by
  let := Module.compHom (cohomology T.X₁ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₂ n) (baseScalars p)
  let := hf
  let g := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
  let g' : cohomology T.X₁ n →ₗ[ℂ] cohomology T.X₂ n :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars p r) x }
  apply LinearMap.finrank_le_finrank_of_surjective (f := g')
  intro x
  exact Ext.covariant_sequence_exact₂ (structureSheaf X) hT x (Subsingleton.elim _ _)

theorem generated_section_H2_le (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    cohomologyDimension S.structureMap (L.tensor M).sheaf 2 ≤
      cohomologyDimension S.structureMap M.sheaf 2 := by
  let I := sectionIdeal k s hs v
  let C : IntegralCurve S := ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩
  let N := (L.tensor M).pullback C.embedding
  let φ : M.sheaf ⟶ (L.tensor M).sheaf := sectionMultiply L M (sectionCombination k s v)
  have : Mono (C := S.scheme.Modules) φ := sectionMultiply_mono L M (sectionCombination k s v) hne
  obtain ⟨hz,hseq⟩ := CartierSequence.exact S.structureMap M (L.tensor M) φ I (by
    intro x
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U,hx,f,tensorFrame L M U.1 e f,?_⟩
    exact (sectionIdeal_on_any_frame k s hs v U e).trans
      (tensor_multiply_ideal L M (sectionCombination k s v) U e f).symm)
  let : Subsingleton (cohomology N.sheaf 2) := ⟨fun x y =>
    (C.cohomology_zero_above_one S A hA N 0 x).trans
      (C.cohomology_zero_above_one S A hA N 0 y).symm⟩
  let : Subsingleton (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj (L.tensor M).sheaf)) 2) :=
    (ClosedPushforward.cohomologyEquiv C.embedding S.structureMap N.sheaf 2).toEquiv.symm.subsingleton
  exact cohomologyDimension_le_of_shortExact S.structureMap hseq 2 (S.H2_finite A hA M)

theorem Surface.power_H2_bounded (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 2 ≤ B := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := cohomologyDimension S.structureMap (L.pow n).sheaf 2
  have hstep (n : ℕ) : f (n+d) ≤ f n := by
    have e := cohomologyDimension_iso S.structureMap (linePowerAdd L d n) 2
    change f (d+n) = cohomologyDimension S.structureMap ((L.pow d).tensor (L.pow n)).sheaf 2 at e
    rw [Nat.add_comm d n] at e
    rw [e]
    exact generated_section_H2_le S L hL (L.pow d) (L.pow n) k s hs v hne hC
  refine ⟨∑ j ∈ Finset.range d, f j,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < d
    · exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_range.mpr hn)
    · have hle : d ≤ n := by omega
      have hlt : n-d < n := by omega
      have hh : f n ≤ f (n-d) := by
        simpa only [Nat.sub_add_cancel hle] using hstep (n-d)
      exact hh.trans (ih _ hlt)

lemma surface_euler_expansion (S : Surface) (M : S.scheme.Modules) :
    eulerCharacteristic S.structureMap 2 M =
      (cohomologyDimension S.structureMap M 0 : ℤ) -
      (cohomologyDimension S.structureMap M 1 : ℤ) +
      (cohomologyDimension S.structureMap M 2 : ℤ) := by
  simp [eulerCharacteristic,Finset.sum_range_succ,sub_eq_add_neg]

theorem Surface.power_H0_quadratic_lower (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ,
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) - 2*B ≤
        2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) := by
  obtain ⟨B,hB⟩ := S.power_H2_bounded L hL
  refine ⟨B,fun n => ?_⟩
  have hq := S.power_euler_quadratic L hL n
  rw [surface_euler_expansion S (L.pow n).sheaf] at hq
  have hle : (cohomologyDimension S.structureMap (L.pow n).sheaf 2 : ℤ) ≤ B := by
    exact_mod_cast hB n
  have hnonneg : (0 : ℤ) ≤ cohomologyDimension S.structureMap (L.pow n).sheaf 1 := Nat.cast_nonneg _
  linarith

end
end MaximalSeshadri.Geometry

end

end OAI
