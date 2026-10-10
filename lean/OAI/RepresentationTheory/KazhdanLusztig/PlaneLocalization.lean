import OAI.RepresentationTheory.KazhdanLusztig.DihedralIntervals

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/

section

namespace KLInvariance.SymmetricPlaneIdeal
universe uk uv
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
noncomputable section

 def ideal (P : Submodule k V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span ((SymmetricAlgebra.ι k V) '' (P : Set V))

 def quotientMap (P : Submodule k V) :
    SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ P) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ P)).comp P.mkQ)

@[simp] theorem quotientMap_ι (P : Submodule k V) (v : V) :
    quotientMap P (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

 theorem ideal_le_ker (P : Submodule k V) : ideal P ≤ RingHom.ker (quotientMap P) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v,hv,rfl⟩
  change quotientMap P (SymmetricAlgebra.ι k V v) = 0
  rw [quotientMap_ι,show P.mkQ v = 0 from (Submodule.Quotient.mk_eq_zero P).mpr hv,map_zero]

 def forward (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) →ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  Ideal.Quotient.liftₐ _ (quotientMap P) (fun _ hz => ideal_le_ker P hz)

 def linearQuotient (P : Submodule k V) : V ⧸ P →ₗ[k]
    (SymmetricAlgebra k V ⧸ ideal P) :=
  P.liftQ ((Ideal.Quotient.mkₐ k (ideal P)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    intro v hv
    apply LinearMap.mem_ker.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨v,hv,rfl⟩))

 def backward (P : Submodule k V) : SymmetricAlgebra k (V ⧸ P) →ₐ[k]
    (SymmetricAlgebra k V ⧸ ideal P) := SymmetricAlgebra.lift (linearQuotient P)

@[simp] theorem forward_mk (P : Submodule k V) (z : SymmetricAlgebra k V) :
    forward P (Ideal.Quotient.mk (ideal P) z) = quotientMap P z := rfl

@[simp] theorem backward_ι_mk (P : Submodule k V) (v : V) :
    backward P (SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v)) =
      Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v) := by
  rw [backward,SymmetricAlgebra.lift_ι_apply]
  rfl

 def quotientEquiv (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  AlgEquiv.ofAlgHom (forward P) (backward P)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := P.mkQ_surjective v
      change forward P (backward P (SymmetricAlgebra.ι k _ (P.mkQ v))) = _
      rw [backward_ι_mk,forward_mk,quotientMap_ι]
      rfl)
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change backward P (forward P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v))) = _
      rw [forward_mk,quotientMap_ι,backward_ι_mk]
      rfl)

@[simp] theorem quotientEquiv_mk_ι (P : Submodule k V) (v : V) :
    quotientEquiv P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) := quotientMap_ι P v

 theorem ι_mem_iff (P : Submodule k V) (v : V) :
    SymmetricAlgebra.ι k V v ∈ ideal P ↔ v ∈ P := by
  constructor
  · intro hv
    have hh := ideal_le_ker P hv
    change quotientMap P (SymmetricAlgebra.ι k V v) = 0 at hh
    rw [quotientMap_ι] at hh
    apply (Submodule.Quotient.mk_eq_zero P).mp
    have he : SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) =
        SymmetricAlgebra.ι k (V ⧸ P) 0 := by simpa only [map_zero] using hh
    by_contra hn
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
    have h := congrArg (SymmetricAlgebra.lift f) he
    rw [SymmetricAlgebra.lift_ι_apply,SymmetricAlgebra.lift_ι_apply,map_zero] at h
    exact hf h
  · intro hv
    exact Ideal.subset_span ⟨v,hv,rfl⟩

 theorem ideal_eq_ker (P : Submodule k V) : ideal P = RingHom.ker (quotientMap P) := by
  apply le_antisymm (ideal_le_ker P)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (quotientEquiv P).injective
  change quotientMap P z = quotientEquiv P 0
  rw [map_zero]
  exact hz

 instance ideal_isPrime (P : Submodule k V) : (ideal P).IsPrime := by
  rw [ideal_eq_ker]
  exact RingHom.ker_isPrime (quotientMap P)

 theorem ideal_span_eq (s : Set V) :
    ideal (Submodule.span k s) = Ideal.span ((SymmetricAlgebra.ι k V) '' s) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨x,hx,rfl⟩
    | zero =>
      rw [map_zero]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul,Algebra.smul_def]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).mul_mem_left _ hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact (ι_mem_iff _ _).mpr (Submodule.subset_span hv)

end
end KLInvariance.SymmetricPlaneIdeal

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {B C : Sheaf.{u,v,w,z} (R := R) G}


theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)] :
    ∃ D : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  let := hC.free O x
  let := hC.finite O x
  obtain ⟨g,jv,hfree,hfinite,hjv⟩ := (j.above x hmax).extend_stalk
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  let := hfinite
  let n := Module.finrank R (LinearMap.ker g)
  let S : Sheaf.{u,v,w,z} (R := R) G := pi (fun _ : Fin n => O.sheaf x)
  let jq : LinearMap.ker g ≃ₗ[R] S.vertex x :=
    (Module.finBasis R (LinearMap.ker g)).equivFun.trans
      (LinearEquiv.piCongrRight (fun _ : Fin n => O.top x)).symm
  let jv' : B.vertex x ≃ₗ[R] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl R (C.vertex x)) jq)
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) :=
    pi_subsingleton_vertex _ y (fun _ => O.support x y (fun hyx => hx (hU hyx hy)))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    apply pi_subsingleton_edge
    intro i
    let := O.support x (G.target e) (fun h => hx (hU h he))
    exact (O.quotient x e).1.subsingleton
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hq : (prod C S).UpperQuotient α :=
    prod_upperQuotient C S α (hC.quotient O) (pi_upperQuotient _ α (fun _ => O.quotient x))
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = (prod C S).lower e (castStalkIso B (prod C S) he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact hjv v ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  refine ⟨prod C S,?_,⟨jj.extend hU x hx hmax α hBq hq jv' hout⟩⟩
  exact .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  (B : Sheaf.{u,v,w,z} (R := R) G)

/-- Actual finite descending decomposition over a local ring. This does not
assume that localization preserves indecomposability. Its explicitly stated
rank-one model criteria must be proved before applying it to a root plane. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free R (B.vertex x))
    (hBfinite : ∀ x, Module.Finite R (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated) :
    ∃ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : Sheaf.{u,v,w,z} (R := R) G,
        ModelSum O.sheaf Set.univ D ∧ Nonempty (Iso B D) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU C hC j
      by_cases hs : s = ∅
      · subst s
        have hh : ((∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
        exact ⟨C,hh ▸ hC,⟨OnIso.ofUniv (hh ▸ j)⟩⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        let := hBfinite x
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum O hU hC j hBq hBf hBg x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') D (heq ▸ hD) (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : OnIso B zero (∅ : Set V) :=
    ⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.Sheaf

end


section

/-! The rank-one plane models over the actual flat local coefficient ring.
The local-ring label condition is later supplied by the plane prime. -/
namespace KLInvariance.BruhatGraph
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)

 theorem exists_outgoing_below (x c : Interval cs u b) (hxc : x < c) :
    ∃ e : Edge cs u b, source cs u b e = x ∧ target cs u b e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 (.single hxz),
      bruhat_trans cs hzc c.property.2⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

end KLInvariance.BruhatGraph

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [IsLocalRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E) (α : E → R)
noncomputable section

 def structureLocalModels
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x c, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (hfl : ∀ c, (structureSheaf G α c).Flabby) : LocalModels (G := G) α where
  sheaf := structureSheaf G α
  free := structureSheaf_free G α
  finite := structureSheaf_finite G α
  quotient := structureSheaf_upperQuotient G α
  generated := structureSheaf_generated G α
  flabby := hfl
  support := structureSheaf_support G α
  top c := structureVertexIso G α c c le_rfl
  minimal c x hx := structureSheaf_minimal G α c hα (fun x => hreach x c) x hx

end
end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us ur
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (R : Type ur) [CommRing R] [Algebra (MvPolynomial σ ℝ) R]
  [Module.Flat (MvPolynomial σ ℝ) R] [IsLocalRing R]
noncomputable section

 def localModels (b : planeSubgroup M cs P)
    (hα : ∀ e, algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal R) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e)) := by
  classical
  let := interval_finite B.system 1 b
  let := Fintype.ofFinite (Edge B.system 1 b)
  exact structureLocalModels _ _ hα (exists_outgoing_below B.system 1 b)
    (fun c => structureSheaf_flat_flabby R _ _ c (B.model_flabby basis b c))

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual plane prime and its localization in the coefficient polynomial
ring of the chosen nondegenerate ambient realization. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def embedLinear : (I → ℝ) →ₗ[ℝ] Extended M where
  toFun := embed M
  map_add' _ _ := by simp [embed]
  map_smul' _ _ := by simp [embed]

 theorem embedLinear_injective : Function.Injective (embedLinear (M := M)) := by
  intro a b hab
  exact congrArg Prod.fst hab

 def planePrime (P : Submodule ℝ (I → ℝ)) : Ideal (MvPolynomial σ ℝ) :=
  Ideal.map (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))))

 instance planePrime_isPrime (P : Submodule ℝ (I → ℝ)) : (planePrime basis P).IsPrime :=
  Ideal.map_isPrime_of_equiv (SymmetricAlgebra.equivMvPolynomial basis)

 theorem linear_mem_planePrime_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    linearPolynomial basis (embed M a) ∈ planePrime basis P ↔ a ∈ P := by
  rw [planePrime,Ideal.mem_map_iff_of_surjective (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).surjective]
  change (∃ z, z ∈ SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))) ∧
    SymmetricAlgebra.equivMvPolynomial basis z =
      SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι ℝ (Extended M) (embed M a))) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have h := (SymmetricAlgebra.equivMvPolynomial basis).injective he
    subst z
    have ha := (SymmetricPlaneIdeal.ι_mem_iff _ _).mp hz
    obtain ⟨b,hb,he⟩ := ha
    have he' : b = a := embedLinear_injective he
    exact he' ▸ hb
  · intro ha
    refine ⟨_,(SymmetricPlaneIdeal.ι_mem_iff _ _).mpr ?_,rfl⟩
    exact ⟨a,ha,rfl⟩

 abbrev PlaneRing (P : Submodule ℝ (I → ℝ)) := Localization.AtPrime (planePrime basis P)

 theorem linear_mem_maximal_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (linearPolynomial basis (embed M a)) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) ↔ a ∈ P := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (planePrime basis P),
    linear_mem_planePrime_iff]

 theorem linear_isUnit_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (linearPolynomial basis (embed M a))) ↔ a ∉ P := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (planePrime basis P)]
  change _ ∉ planePrime basis P ↔ _
  rw [linear_mem_planePrime_iff]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem modelLabel_mem_maximal (b : planeSubgroup M cs P) (e : Edge B.system 1 b) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) := by
  apply (linear_mem_maximal_iff basis P _).mpr
  apply (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs _)).mp
  exact (label B.system 1 b e).property

 def localizedModels (b : planeSubgroup M cs P) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e)) :=
  B.localModels basis (PlaneRing basis P) b (B.modelLabel_mem_maximal basis b)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual finite relative lower ideal in a maximal root-plane coset.
No order-reflection identification with ambient comparability is used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  (a₀ b : W)
noncomputable section

 def CosetVertex := {d : planeSubgroup M cs P // BruhatLE B.system 1 d ∧
    BruhatLE cs ((d:W)*a₀) b}

 instance cosetOrder : PartialOrder (B.CosetVertex a₀ b) where
  le x y := BruhatLE B.system x.val y.val
  le_refl x := bruhat_refl B.system x.val
  le_trans _ _ _ := bruhat_trans B.system
  le_antisymm x y hxy hyx := Subtype.ext (bruhat_antisymm B.system hxy hyx)

 def cosetAmbient (x : B.CosetVertex a₀ b) : Interval cs 1 b :=
  ⟨(x.val:W)*a₀,one_bruhat cs _,x.property.2⟩

 theorem cosetAmbient_injective : Function.Injective (B.cosetAmbient a₀ b) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_right_cancel (congrArg Subtype.val h)

 instance cosetFinite : Finite (B.CosetVertex a₀ b) := by
  let := interval_finite cs 1 b
  exact Finite.of_injective _ (B.cosetAmbient_injective a₀ b)

 def CosetEdge := {p : B.CosetVertex a₀ b × B.CosetVertex a₀ b //
    BruhatStep B.system p.1.val p.2.val}

 def cosetGraph : OrderedGraph (B.CosetVertex a₀ b) (B.CosetEdge a₀ b) where
  source e := e.val.1
  target e := e.val.2
  increasing e := ⟨.single e.property,fun h => not_lt_of_ge
    (length_le_of_bruhat B.system h) e.property.1⟩

variable (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))

 def cosetEdgeAmbient (e : B.CosetEdge a₀ b) : Edge cs 1 b :=
  ⟨(B.cosetAmbient a₀ b e.val.1,B.cosetAmbient a₀ b e.val.2),
    (B.coset_step_iff hmin _ _).mpr e.property⟩

 def cosetGraphMap : GraphMap (B.cosetGraph a₀ b) (graph cs 1 b) where
  vertex := B.cosetAmbient a₀ b
  edge := B.cosetEdgeAmbient a₀ b hmin
  source _ := rfl
  target _ := rfl

 include hmin in
 theorem coset_lower {d : planeSubgroup M cs P} {x : B.CosetVertex a₀ b}
    (hx : BruhatLE B.system d x.val) : BruhatLE cs ((d:W)*a₀) b :=
  bruhat_trans cs (B.coset_bruhat hmin hx) x.property.2

 include hmin in
 theorem coset_outgoing_below (x c : B.CosetVertex a₀ b) (hxc : x<c) :
    ∃ e : B.CosetEdge a₀ b, (B.cosetGraph a₀ b).source e=x ∧
      (B.cosetGraph a₀ b).target e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : B.CosetVertex a₀ b := ⟨z,one_bruhat B.system z,
      B.coset_lower a₀ b hmin hzc⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

 theorem coset_lift_live (e : Edge cs 1 b)
    (he : label cs 1 b e ∈ planeSubgroup M cs P)
    (x : B.CosetVertex a₀ b) (hx : B.cosetAmbient a₀ b x=source cs 1 b e) :
    ∃ a : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin a=e ∧
      (B.cosetGraph a₀ b).source a=x := by
  let t : planeSubgroup M cs P := ⟨label cs 1 b e,he⟩
  have hy : ((t*x.val : planeSubgroup M cs P):W)*a₀ = (target cs 1 b e).val := by
    change (label cs 1 b e*(x.val:W))*a₀ = _
    rw [mul_assoc,show (x.val:W)*a₀=(source cs 1 b e).val from congrArg Subtype.val hx]
    exact label_mul_source cs 1 b e
  let y : B.CosetVertex a₀ b := ⟨t*x.val,one_bruhat B.system _,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hye : B.cosetAmbient a₀ b y=target cs 1 b e := Subtype.ext hy
  have hs : BruhatStep B.system x.val y.val := by
    apply (B.coset_step_iff hmin _ _).mp
    change BruhatStep cs (B.cosetAmbient a₀ b x).val (B.cosetAmbient a₀ b y).val
    rw [hx,hye]
    exact e.property
  refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
  apply Subtype.ext
  exact Prod.ext hx hye

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Actual plane localization of the boundary-constructed sheaf. Its relative
coset restriction is free, generated and flabby with upper quotient maps;
no character or upward-kernel freeness theorem is used. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem edge_subsingleton_of_unit (α : E → R) (hq : B.UpperQuotient α)
    (e : E) (he : IsUnit (α e)) : Subsingleton (B.edge e) := by
  obtain ⟨a,ha⟩ := he
  have hz : ∀ v : B.edge e, v=0 := by
    intro v
    obtain ⟨w,rfl⟩ := (hq e).1 v
    apply ((hq e).2 w).mpr
    refine ⟨(↑a⁻¹ : R) • w,?_⟩
    rw [← ha,smul_smul]
    simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetLabel (e : B.CosetEdge a₀ b) : PlaneRing basis P :=
  algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e))

 def localizedCoset (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b)) :
    Sheaf (R := PlaneRing basis P) (B.cosetGraph a₀ b) :=
  (C.baseChange (PlaneRing basis P)).pullback (B.cosetGraphMap a₀ b hmin)

 omit [Fintype σ] in
 theorem polynomialLabel_unit_iff (e : Edge cs 1 b) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (polynomialLabel cs 1 b basis e)) ↔ label cs 1 b e ∉ planeSubgroup M cs P := by
  change IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (linearPolynomial basis (embed M (BruhatGraph.root cs 1 b e).val))) ↔ _
  rw [linear_isUnit_iff]
  have hr := positiveRoot_represents M cs ⟨label cs 1 b e,label_isReflection cs 1 b e⟩
  exact not_congr (Represents.planeSubgroup_mem_iff M cs hr).symm

 omit [Fintype σ] in
 theorem localizedCoset_quotient (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) :
    (B.localizedCoset basis a₀ b hmin C).UpperQuotient (B.cosetLabel basis a₀ b hmin) :=
  (C.baseChange (PlaneRing basis P)).pullback_quotient (B.cosetGraphMap a₀ b hmin)
    (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialLabel cs 1 b basis e))
    (C.baseChange_upperQuotient (PlaneRing basis P) (polynomialLabel cs 1 b basis) hq)

 omit [Fintype σ] in
 theorem localizedCoset_generated (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hg : C.Generated) : (B.localizedCoset basis a₀ b hmin C).Generated :=
  (C.baseChange (PlaneRing basis P)).pullback_generated _
    (C.baseChange_generated (PlaneRing basis P) hg)

 omit [Fintype σ] in
 theorem localizedCoset_flabby (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) (hf : C.Flabby) :
    (B.localizedCoset basis a₀ b hmin C).Flabby := by
  let := interval_finite cs 1 b
  apply (C.baseChange (PlaneRing basis P)).pullback_flabby_live _
    (C.baseChange_flabby (PlaneRing basis P) hf) (B.cosetAmbient_injective a₀ b)
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · exact B.coset_lift_live a₀ b hmin

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The relative rank-one structure models are natural under full strictly
order-compatible graph embeddings, with exactly the pulled-back labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} {W : Type uw} [PartialOrder W]
  {F : Type uf} {H : OrderedGraph W F}
noncomputable section

 def propPiEquiv (N : Type*) [AddCommGroup N] [Module R N]
    {p q : Prop} (h : p ↔ q) : (PLift p → N) ≃ₗ[R] (PLift q → N) where
  toFun v t := v ⟨h.mpr t.down⟩
  invFun v t := v ⟨h.mp t.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem moduleEq_pi_apply {X : Type*} (p : X → Prop) {x y : X} (h : x=y)
    (v : PLift (p x) → R) (t : PLift (p y)) :
    moduleEq (congrArg (fun z => ModuleCat.of R (PLift (p z) → R)) h) v t =
      v ⟨h.symm ▸ t.down⟩ := by
  subst y
  rfl

 def structurePullbackIso (f : GraphMap G H) (α : F → R) (c : V)
    (ho : ∀ x y, f.vertex x ≤ f.vertex y ↔ x ≤ y) :
    Iso ((structureSheaf H α (f.vertex c)).pullback f)
      (structureSheaf G (fun e => α (f.edge e)) c) where
  vertex x := propPiEquiv R (ho x c)
  edge e := propPiEquiv (R ⧸ Ideal.span {α (f.edge e)}) (by
    rw [← f.target e]; exact ho (G.target e) c)
  lower e v := by
    change (PLift (f.vertex (G.source e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.source e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.source e) v _
  upper e v := by
    change (PLift (f.vertex (G.target e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.target e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.target e) v _

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Rank-one models on the actual finite relative lower ideal in an ambient
plane coset. The ideal need not have a greatest element. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetInto (d : planeSubgroup M cs P) (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    B.CosetVertex a₀ b → Interval B.system 1 d := fun x => ⟨x.val,x.property.1,hd x⟩

 def cosetIntoEdge (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    Edge B.system 1 d := ⟨(B.cosetInto a₀ b d hd e.val.1,B.cosetInto a₀ b d hd e.val.2),e.property⟩

 def cosetIntoGraph (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    GraphMap (B.cosetGraph a₀ b) (graph B.system 1 d) where
  vertex := B.cosetInto a₀ b d hd
  edge := B.cosetIntoEdge a₀ b d hd
  source _ := rfl
  target _ := rfl

 theorem cosetInto_injective (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    Function.Injective (B.cosetInto a₀ b d hd) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Interval B.system 1 d => z.val) h

 theorem coset_label_eq (e : B.CosetEdge a₀ b) :
    label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) = (e.val.2.val : W)*(e.val.1.val:W)⁻¹ := by
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

 theorem coset_modelLabel_eq (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    B.modelLabel basis d (B.cosetIntoEdge a₀ b d hd e) =
      polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e) := by
  have ht : (⟨(label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val,
      (B.reflection_iff _).mp (label_isReflection B.system 1 d _)⟩ : {t : W // cs.IsReflection t}) =
      ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),label_isReflection cs 1 b _⟩ := by
    apply Subtype.ext
    change (label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val =
      label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)
    rw [B.coset_label_eq a₀ b hmin e]
    rfl
  exact congrArg (fun t : {t : W // cs.IsReflection t} =>
    linearPolynomial basis (embed M (positiveRoot M cs t).val)) ht

 include hmin in
 theorem coset_model_flabby (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).Flabby := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  obtain ⟨d,hd⟩ := Dihedral.exists_common_upper B.system
    (Finset.univ.image (fun x : B.CosetVertex a₀ b => x.val))
  have hbnd (x : B.CosetVertex a₀ b) : BruhatLE B.system x.val d :=
    hd _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
  let f := B.cosetIntoGraph a₀ b d hbnd
  let α : Edge B.system 1 d → PlaneRing basis P := fun e =>
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis d e)
  let C := structureSheaf (graph B.system 1 d) α (f.vertex c)
  have hfl : C.Flabby := (B.localizedModels basis d).flabby (f.vertex c)
  let := interval_finite B.system 1 d
  have hpull : (C.pullback f).Flabby := by
    apply C.pullback_flabby_live f hfl (B.cosetInto_injective a₀ b d hbnd)
      {e | target B.system 1 d e ≤ f.vertex c}
    · intro e he
      exact structureSheaf_edge_subsingleton _ α (f.vertex c) e he
    · intro e he x hx
      have hlow : BruhatLE B.system (target B.system 1 d e).val c.val := he
      let y : B.CosetVertex a₀ b := ⟨(target B.system 1 d e).val,
        (target B.system 1 d e).property.1,B.coset_lower a₀ b hmin hlow⟩
      have hye : f.vertex y=target B.system 1 d e := rfl
      have hs : BruhatStep B.system x.val y.val := by
        change BruhatStep B.system (f.vertex x).val (f.vertex y).val
        rw [hx,hye]
        exact e.property
      refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
      exact Subtype.ext (Prod.ext hx hye)
  have hh := (structurePullbackIso f α c (fun _ _ => Iff.rfl)).flabby hpull
  have hα : (fun e => α (f.edge e)) = B.cosetLabel basis a₀ b hmin := by
    funext e
    exact congrArg (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P))
      (B.coset_modelLabel_eq basis a₀ b hmin d hbnd e)
  rwa [hα] at hh

 def cosetModels : LocalModels (G := B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) :=
  structureLocalModels _ _
    (fun e => (linear_mem_maximal_iff basis P _).mpr (by
      apply (Represents.planeSubgroup_mem_iff M cs
        (positiveRoot_represents M cs ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),
          label_isReflection cs 1 b _⟩)).mp
      change label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) ∈ planeSubgroup M cs P
      rw [B.coset_label_eq a₀ b hmin e]
      exact (planeSubgroup M cs P).mul_mem e.val.2.val.property
        ((planeSubgroup M cs P).inv_mem e.val.1.val.property)))
    (B.coset_outgoing_below a₀ b hmin) (B.coset_model_flabby basis a₀ b hmin)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Partial upward kernels of the actual rank-one model, with their embedded
edge images. No character or freeness property of BMP sheaves is assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

 def supportedOutgoing (x : V) (F : Set (Outgoing (G := G) x)) : Finset (Outgoing (G := G) x) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ F ∧ G.target e.val ≤ c)

 def kernelProduct (x : V) (F : Set (Outgoing (G := G) x)) : R :=
  ∏ e ∈ supportedOutgoing G c x F, α e.val

 theorem structure_kernel_iff_dvd (x : V) (hx : x ≤ c)
    (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val)))
    (v : (structureSheaf G α c).vertex x) :
    v ∈ (structureSheaf G α c).upwardKernel x F ↔ kernelProduct G α c x F ∣ v ⟨hx⟩ := by
  classical
  constructor
  · intro hv
    apply Finset.prod_dvd_of_isRelPrime hrel
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    have hvv := congrFun (hv e hh.1) ⟨hh.2⟩
    rcases e with ⟨e,he⟩
    subst x
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hvv)
  · intro hv e he
    funext h
    have hh : e ∈ supportedOutgoing G c x F :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,h.down⟩
    have hd : α e.val ∣ v ⟨hx⟩ := (Finset.dvd_prod_of_mem (fun a => α a.val) hh).trans hv
    rcases e with ⟨e,heq⟩
    subst x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)

 theorem structure_kernel_product (x : V) (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val))) :
    (structureSheaf G α c).upwardKernel x F =
      kernelProduct G α c x F • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  by_cases hx : x ≤ c
  · rw [structure_kernel_iff_dvd G α c x hx F hrel]
    constructor
    · rintro ⟨r,hr⟩
      refine ⟨fun _ => r,Submodule.mem_top,?_⟩
      funext h
      exact hr.symm
    · rintro ⟨w,_,hw⟩
      exact ⟨w ⟨hx⟩,(congrFun hw ⟨hx⟩).symm⟩
  · let _ := structureSheaf_support G α c x hx
    constructor
    · intro _
      exact ⟨0,Submodule.mem_top,Subsingleton.elim _ _⟩
    · intro _
      rw [Subsingleton.elim v 0]
      exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

 theorem lower_surjective_of_generated (B : Sheaf (R := R) G) (hg : B.Generated)
    (hu : ∀ e, Function.Surjective (B.upper e)) (e : E) : Function.Surjective (B.lower e) := by
  intro v
  obtain ⟨w,hw⟩ := hu e v
  obtain ⟨s,hs,ht⟩ := hg (G.target e) w
  refine ⟨s (G.source e),?_⟩
  rw [hs e (Set.mem_univ _) (Set.mem_univ _),ht,hw]

variable [DecompositionMonoid R] [Fintype E] (α : E → R) (c : V)

 theorem structure_lower_image (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (hrel : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.source e) F).map ((structureSheaf G α c).lower e) =
      kernelProduct G α c (G.source e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  apply LinearMap.range_eq_top.mpr
  exact lower_surjective_of_generated _ (structureSheaf_generated G α c)
    (fun a => (structureSheaf_upperQuotient G α c a).1) e

 theorem structure_upper_image (e : E) (F : Set (Outgoing (G := G) (G.target e)))
    (hrel : (supportedOutgoing G c (G.target e) F : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.target e) F).map ((structureSheaf G α c).upper e) =
      kernelProduct G α c (G.target e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  exact LinearMap.range_eq_top.mpr (structureSheaf_upperQuotient G α c e).1

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Distinct prime root labels remain relatively prime after genuine prime
localization. The prime may contain both labels; coprimality here is gcd
coprimality, not comaximality. -/
namespace KLInvariance.LocalizationRelativePrime
variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

omit [IsDomain A] in
 theorem not_dvd_map {a b : A} (ha : Prime a) (hap : a ∈ p) (hab : ¬a ∣ b) :
    ¬ algebraMap A (Localization.AtPrime p) a ∣ algebraMap A (Localization.AtPrime p) b := by
  intro h
  obtain ⟨s,hs,hdiv⟩ := (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_dvd_map.mp h
  rcases ha.dvd_mul.mp hdiv with has | hab'
  · exact hs (p.mem_of_dvd has hap)
  · exact hab hab'

 theorem map_prime {a : A} (ha : Prime a) (hap : a ∈ p) :
    Prime (algebraMap A (Localization.AtPrime p) a) := by
  apply (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_prime ha
  · change algebraMap A (Localization.AtPrime p) a ≠ 0
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective A (Localization.AtPrime p)).ne ha.ne_zero
  · change ¬IsUnit (algebraMap A (Localization.AtPrime p) a)
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ p]
    exact not_not_intro hap

 theorem map_relPrime {a b : A} (ha : Prime a) (hab : ¬a ∣ b) :
    IsRelPrime (algebraMap A (Localization.AtPrime p) a)
      (algebraMap A (Localization.AtPrime p) b) := by
  by_cases hap : a ∈ p
  · exact ((map_prime p ha hap).irreducible.isRelPrime_iff_not_dvd).mpr (not_dvd_map p ha hap hab)
  · exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p a).mpr hap).isRelPrime_left

end KLInvariance.LocalizationRelativePrime

end


section

/-! The local product-kernel lemma on the actual maximal-plane coset.
All regularity hypotheses come from distinct genuine incident reflections. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
open scoped Pointwise
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetEdgeAmbient_injective : Function.Injective (B.cosetEdgeAmbient a₀ b hmin) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.1) h)
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.2) h)

 theorem cosetLabel_relPrime {e f : B.CosetEdge a₀ b} (hef : e ≠ f)
    (hs : (B.cosetGraph a₀ b).source e = (B.cosetGraph a₀ b).source f) :
    IsRelPrime (B.cosetLabel basis a₀ b hmin e) (B.cosetLabel basis a₀ b hmin f) := by
  apply LocalizationRelativePrime.map_relPrime (planePrime basis P)
    (polynomialLabel_prime cs 1 b basis _)
  intro hd
  apply hef
  apply B.cosetEdgeAmbient_injective a₀ b hmin
  apply eq_of_label_source_eq cs 1 b (label_eq_of_polynomialLabel_dvd cs 1 b basis hd)
  exact congrArg (B.cosetAmbient a₀ b) hs

 theorem coset_supported_pairwise [Fintype (B.CosetEdge a₀ b)]
    (c x : B.CosetVertex a₀ b)
    (F : Set (Outgoing (G := B.cosetGraph a₀ b) x)) :
    (supportedOutgoing (B.cosetGraph a₀ b) c x F :
      Set (Outgoing (G := B.cosetGraph a₀ b) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => B.cosetLabel basis a₀ b hmin e.val)) := by
  intro e _ f _ hef
  exact B.cosetLabel_relPrime basis a₀ b hmin
    (fun h => hef (Subtype.ext h)) (e.property.trans f.property.symm)

 theorem coset_kernel_product [Fintype (B.CosetEdge a₀ b)]
    (c x : B.CosetVertex a₀ b) (F : Set (Outgoing (G := B.cosetGraph a₀ b) x)) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).upwardKernel x F =
      kernelProduct (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c x F •
        (⊤ : Submodule (PlaneRing basis P)
          ((structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).vertex x)) :=
  structure_kernel_product _ _ _ _ _ (B.coset_supported_pairwise basis a₀ b hmin c x F)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetUpperVertex (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    Interval cs u b := ⟨(x.val:W)*a₀,hx,x.property.2⟩

 theorem outgoing_step (x : B.CosetVertex a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatStep B.system x.val f.val.val.2.val := by
  rcases f with ⟨f,hf⟩
  change f.val.1=x at hf
  subst x
  exact f.property

 include hmin in
 theorem outgoing_upper (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatLE cs u ((f.val.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr (B.outgoing_step x f)))

 def scheduledOutgoing (φ : Interval cs u b ≃o Interval cs' u' b')
    (α : PositiveRoot M' cs') (x : B.CosetVertex a₀ b)
    (hx : BruhatLE cs u ((x.val:W)*a₀)) : Set (Outgoing (G := B.cosetGraph a₀ b) x) :=
  {f | ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α
    (φ (B.cosetUpperVertex f.val.val.2 (B.outgoing_upper hmin x hx f))).val = 1}

 theorem outgoing_target_injective (x : B.CosetVertex a₀ b) :
    Function.Injective (fun f : Outgoing (G := B.cosetGraph a₀ b) x => f.val.val.2) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (f.property.trans g.property.symm) h

 theorem supported_card_count [Fintype (B.CosetEdge a₀ b)]
    (φ : Interval cs u b ≃o Interval cs' u' b') (α : PositiveRoot M' cs')
    (a x c : B.CosetVertex a₀ b) (hax : a ≤ x)
    (ha : BruhatLE cs u ((a.val:W)*a₀)) :
    let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
    let inc := B.cosetIntervalMap hmin ha c.property.2
    (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
      ∑ᶠ z : Interval B.system a.val c.val,
        ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val := by
  classical
  let := interval_finite B.system a.val c.val
  let := Fintype.ofFinite (Interval B.system a.val c.val)
  let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
  let inc := B.cosetIntervalMap hmin ha c.property.2
  let F := B.scheduledOutgoing hmin φ α x hx
  let s := supportedOutgoing (B.cosetGraph a₀ b) c x F
  change s.card = ∑ᶠ z : Interval B.system a.val c.val,
    ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val
  rw [finsum_eq_sum_of_fintype]
  rw [show s.card=(∑ _ ∈ s,(1:ℕ)) by simp]
  let idx (f : Outgoing (G := B.cosetGraph a₀ b) x) (hf : f ∈ s) :
      Interval B.system a.val c.val :=
    ⟨f.val.val.2.val,bruhat_trans B.system hax (.single (B.outgoing_step x f)),
      (Finset.mem_filter.mp hf).2.2⟩
  apply Finset.sum_bij_ne_zero (fun f hf _ => idx f hf)
  · intro _ _ _
    exact Finset.mem_univ _
  · intro f hf _ g hg _ h
    have hz : f.val.val.2.val=g.val.val.2.val := congrArg (fun z : Interval B.system a.val c.val => z.val) h
    exact B.outgoing_target_injective x (Subtype.ext hz)
  · intro z _ hz
    have hsz : BruhatStep cs' (φ (B.cosetUpperVertex x hx)).val (φ (inc z)).val := by
      by_contra hn
      exact hz (by simp only [ambientAfterIndicator,dite_eq_right hn])
    have hcz := (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mp hsz
    have hs : BruhatStep B.system x.val z.val := (B.coset_step_iff hmin _ _).mp hcz
    let y : B.CosetVertex a₀ b := ⟨z.val,one_bruhat B.system z.val,
      bruhat_trans cs (B.coset_bruhat hmin z.property.2) c.property.2⟩
    let f : Outgoing (G := B.cosetGraph a₀ b) x := ⟨⟨(x,y),hs⟩,rfl⟩
    have hfF : f ∈ F := by
      change ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val=1
      unfold ambientAfterIndicator at hz ⊢
      split_ifs at hz ⊢ <;> omega
    have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfF,z.property.2⟩
    exact ⟨f,hfs,by omega,rfl⟩
  · intro f hf _
    exact ((Finset.mem_filter.mp hf).2.1).symm

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

/-- The combinatorial factor already constructed from ambient inversion
pairs is exactly the intrinsic relative dihedral edge degree. -/
 theorem planeWeight_coset_edge {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    (planeWeight ((x:W)*a₀) (B.edgeRoot hxy) P).toNat =
      (B.system.length y-B.system.length x-1)/2 := by
  classical
  let α := B.edgeRoot hxy
  obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
    by_cases h : α=B.left
    · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
    · exact ⟨B.left,h,B.left_mem⟩
  have hplane : rootPlane α β=P :=
    (rootPlane_eq_of_mem B.left B.right α β B.distinct
      (B.plane_eq.ge (B.edgeRoot_plane hxy)) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq
  have ha : ¬rootInverted ((x:W)*a₀) α := by
    rw [show α=graphRoot ((B.coset_step_iff hmin x y).mpr hxy) from B.edgeRoot_coset hmin hxy]
    exact graphRoot_not_inverted_source _
  have href : rootRef α=(y:W)*(x:W)⁻¹ :=
    (rootReflection_represents M cs α).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
  have hends : rootRef α*((x:W)*a₀)=(y:W)*a₀ := by rw [href]; group
  have h := planeWeight_relative_degree ((x:W)*a₀) α β hαβ ha
  rw [hplane,hends,B.coset_length_eq hmin x,B.coset_length_eq hmin y] at h
  have hn := planeWeight_nonneg ((x:W)*a₀) α P
  have hlen := hxy.1
  have hc : ((planeWeight ((x:W)*a₀) α P).toNat:ℤ)=planeWeight ((x:W)*a₀) α P :=
    Int.toNat_of_nonneg hn
  change (planeWeight ((x:W)*a₀) α P).toNat = _
  omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 include hmin in
 theorem cosetEdge_target_upper (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) : BruhatLE cs u ((e.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr e.property))

 def mappedCosetRoot (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    PositiveRoot M' cs' :=
  graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ
    (B.cosetUpperVertex e.val.1 hx)
    (B.cosetUpperVertex e.val.2 (B.cosetEdge_target_upper hmin e hx))).mpr
    ((B.coset_step_iff hmin _ _).mpr e.property))

 def scheduledLower (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.1) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.1 hx

 def scheduledUpper (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.2) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.2
    (B.cosetEdge_target_upper hmin e hx)

 theorem scheduledLower_self (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) ∉ B.scheduledLower hmin φ e hx := by
  change ambientAfterIndicator _ (graphRoot _) _ ≠ 1
  rw [ambientAfterIndicator_edge_self]
  omega

 theorem supported_count_difference [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) (hyc : e.val.2 ≤ c) :
    (supportedOutgoing (B.cosetGraph a₀ b) c e.val.1 (B.scheduledLower hmin φ e hx)).card =
      (supportedOutgoing (B.cosetGraph a₀ b) c e.val.2 (B.scheduledUpper hmin φ e hx)).card+
        (planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat := by
  let x := e.val.1
  let y := e.val.2
  let α := B.mappedCosetRoot hmin φ e hx
  have hxy : BruhatLE B.system x.val y.val := .single e.property
  have hxc : BruhatLE B.system x.val c.val := bruhat_trans B.system hxy hyc
  let yy : Interval B.system x.val c.val := ⟨y.val,hxy,hyc⟩
  have h := B.transported_count_difference_all hmin hxc hx c.property.2 φ yy e.property
  rw [B.planeWeight_coset_edge hmin e.property]
  change (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
    (supportedOutgoing (B.cosetGraph a₀ b) c y
      (B.scheduledOutgoing hmin φ α y (B.cosetEdge_target_upper hmin e hx))).card+_
  rw [B.supported_card_count hmin φ α x x c (bruhat_refl B.system x.val) hx,
    B.supported_card_count hmin φ α x y c hxy hx]
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.BruhatGraph
open TitsSpace MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def ambientLater (α : PositiveRoot M' cs') : Set (Edge cs 1 b) :=
  {e | ∃ hx : BruhatLE cs u (source cs 1 b e).val,
    ambientAfterIndicator (φ ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩).val α
      (φ ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),
        (target cs 1 b e).property.2⟩).val = 1}

end
end KLInvariance.BruhatGraph

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledOutgoing_eq (α : PositiveRoot M' cs')
    (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    B.scheduledOutgoing hmin φ α x hx =
      {f | B.cosetEdgeAmbient a₀ b hmin f.val ∈ ambientLater φ α} := by
  ext f
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=x at hs
  subst s
  change (_=1) ↔ ∃ hh : BruhatLE cs u ((x.val:W)*a₀), _=1
  constructor
  · intro h
    exact ⟨hx,h⟩
  · rintro ⟨_,h⟩
    exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Reduction of a root plane along one root is genuinely one-dimensional.
The scalar comparing two nonparallel reduced roots is a nonzero element of
the original base field, hence a unit after every coefficient localization. -/
namespace KLInvariance.PlaneReduction
universe uk uv ua
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
  {A : Type ua} [CommRing A] [Algebra k A]

 theorem scalar_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) :
    ∃ r : k, r ≠ 0 ∧ l c = r • l b := by
  obtain ⟨s,r,hr⟩ := Submodule.mem_span_pair.mp hc
  have hr0 : r ≠ 0 := by
    intro hz
    apply hca
    rw [← hr,hz,zero_smul,add_zero]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_singleton a))
  refine ⟨r,hr0,?_⟩
  rw [← hr,map_add,map_smul,map_smul,ha,smul_zero,zero_add]

 theorem associated_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) : Associated (l c) (l b) := by
  obtain ⟨r,hr,he⟩ := scalar_reduction l ha hc hca
  rw [he,Algebra.smul_def]
  exact associated_unit_mul_left _ _ ((hr.isUnit).map (algebraMap k A))

end KLInvariance.PlaneReduction

end


section

/-! Actual root labels in the localized edge quotient: every nonparallel
root in a given plane has a reduced label associated to any chosen one. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def localizedLinear (P : Submodule ℝ (I → ℝ)) : (I → ℝ) →ₗ[ℝ] PlaneRing basis P :=
  (IsScalarTower.toAlgHom ℝ (MvPolynomial σ ℝ) (PlaneRing basis P)).toLinearMap.comp
    ((linearPolynomial basis).comp (embedLinear (M := M)))

 def localizedEdgeIdeal (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) : Ideal (PlaneRing basis P) :=
  Ideal.span {localizedLinear basis P a}

 abbrev LocalizedEdgeRing (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :=
  PlaneRing basis P ⧸ localizedEdgeIdeal basis P a

 def localizedReduction (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    (I → ℝ) →ₗ[ℝ] LocalizedEdgeRing basis P a :=
  (Ideal.Quotient.mkₐ ℝ (localizedEdgeIdeal basis P a)).toLinearMap.comp
    (localizedLinear basis P)

 theorem localizedReduction_self (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    localizedReduction basis P a a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

 theorem positiveRoot_not_line {a c : PositiveRoot M cs} (hca : c ≠ a) :
    c.val ∉ Submodule.span ℝ ({a.val} : Set (I → ℝ)) := by
  intro h
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp (positiveRoots_independent c a hca)).2 r hr

 theorem localizedReduction_associated (P : Submodule ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) (hc : c.val ∈ rootPlane a b) (hca : c ≠ a) :
    Associated (localizedReduction basis P a.val c.val)
      (localizedReduction basis P a.val b.val) :=
by
  exact @PlaneReduction.associated_reduction ℝ _ (I → ℝ) _ _
    (LocalizedEdgeRing basis P a.val) _ _ (localizedReduction basis P a.val)
    a.val b.val c.val (localizedReduction_self basis P a.val) hc
    (positiveRoot_not_line hca)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def polynomialRoot (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M a.val))

 theorem polynomialRoot_homogeneous (a : PositiveRoot M cs) :
    polynomialRoot cs basis a ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialRoot
  rw [← basis.sum_repr (embed M a.val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

omit [Fintype σ] in
 theorem polynomialRoot_prime (a : PositiveRoot M cs) : Prime (polynomialRoot cs basis a) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact a.property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype σ] in
 theorem polynomialRoot_not_dvd {a r : PositiveRoot M cs} (h : r ≠ a) :
    ¬ polynomialRoot cs basis a ∣ polynomialRoot cs basis r := by
  rintro ⟨z,hz⟩
  apply embed_not_rootLine a r h
  apply (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp
  refine ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialRoot] using hz


 def edgeFactorLift (x : W) (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  ∏ P : (planeWeight x a).support,
    polynomialRoot cs basis (planeRoot x a P) ^ (planeWeight x a P.val).toNat

 theorem edgeFactorLift_homogeneous (x : W) (a : PositiveRoot M cs) :
    edgeFactorLift cs basis x a ∈ polynomialGrading ℝ σ (edgeFactorDegree x a : ℤ) := by
  classical
  have h := SetLike.prod_pow_mem_graded (polynomialGrading ℝ σ)
    (fun _ : (planeWeight x a).support => (1 : ℤ))
    (fun P => polynomialRoot cs basis (planeRoot x a P))
    (fun P => (planeWeight x a P.val).toNat)
    (F := Finset.univ) (fun P _ => polynomialRoot_homogeneous cs basis (planeRoot x a P))
  simpa only [edgeFactorLift,edgeFactorDegree,Nat.cast_sum,nsmul_eq_mul,mul_one] using h

omit [Fintype σ] in
 theorem edgeFactorLift_not_dvd (x : W) (a : PositiveRoot M cs) :
    ¬ polynomialRoot cs basis a ∣ edgeFactorLift cs basis x a := by
  classical
  apply (polynomialRoot_prime cs basis a).not_dvd_finsetProd
  intro P _ h
  exact polynomialRoot_not_dvd cs basis (planeRoot_ne x a P)
    ((polynomialRoot_prime cs basis a).dvd_of_dvd_pow h)

omit [Fintype σ] in
 theorem edgeFactorLift_reduction (x : W) (a : PositiveRoot M cs) :
    Ideal.Quotient.mk (EdgeAlgebra.rootIdeal (k := ℝ) (embed M a.val))
      ((SymmetricAlgebra.equivMvPolynomial basis).symm (edgeFactorLift cs basis x a)) =
      edgeFactor x a := by
  simp only [edgeFactorLift,map_prod,map_pow,polynomialRoot,AlgEquiv.symm_apply_apply,
    edgeFactor,reducedPlaneRoot]

variable (u b : W) (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)

theorem rootRef_root (e : Edge cs u b) :
    rootRef (root cs u b e) = label cs u b e :=
  congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨label cs u b e,label_isReflection cs u b e⟩)

 theorem root_not_inverted (e : Edge cs u b) :
    ¬ rootInverted (source cs u b e).val (root cs u b e) := by
  intro h
  have hi := ((rootReflection_represents M cs (root cs u b e)).inversion_iff
    (root cs u b e).property.2 (source cs u b e).val).mp h
  have hl := hi.2
  change cs.length (rootRef (root cs u b e) * (source cs u b e).val) <
    cs.length (source cs u b e).val at hl
  rw [rootRef_root, label_mul_source] at hl
  exact (not_lt_of_ge e.property.1.le) hl

 theorem edgeFactorDegree_edge (e : Edge cs u b) :
    2 * (edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) =
      (cs.length (target cs u b e).val : ℤ) - cs.length (source cs u b e).val - 1 := by
  rw [edgeFactorDegree_cast]
  have h := sum_planeWeight (source cs u b e).val (root cs u b e)
    (root_not_inverted cs u b e)
  rwa [rootRef_root, label_mul_source] at h

/-- Multiplication by the genuine plane product on the actual edge module. -/
 def edgeFactorMap (e : Edge cs u b) : B.sheaf.edge e →ₗ[Coefficient (σ := σ)] B.sheaf.edge e :=
  LinearMap.lsmul (Coefficient (σ := σ)) (B.sheaf.edge e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))

 theorem edgeFactorMap_graded (e : Edge cs u b) (n : ℤ) (v : B.sheaf.edge e)
    (hv : v ∈ (B.sheaf.edge e).piece n) :
    edgeFactorMap cs basis u b hub B e v ∈ (B.sheaf.edge e).piece
      (n + edgeFactorDegree (source cs u b e).val (root cs u b e)) := by
  simpa only [edgeFactorMap,LinearMap.lsmul_apply,vadd_eq_add,add_comm] using
    SetLike.GradedSMul.smul_mem (edgeFactorLift_homogeneous cs basis
      (source cs u b e).val (root cs u b e)) hv

omit [Fintype σ] in
 theorem edgeFactorLift_regular (e : Edge cs u b) :
    Function.Injective (fun v : B.sheaf.edge e =>
      edgeFactorLift cs basis (source cs u b e).val (root cs u b e) • v) := by
  let := B.free ((graph cs u b).target e)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target e)))
    (B.sheaf.upper e).map (B.quotient e).1
    (polynomialLabel cs u b basis e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))
    (polynomialLabel_prime cs u b basis e)
    (edgeFactorLift_not_dvd cs basis (source cs u b e).val (root cs u b e)) (B.quotient e).2

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.LocalProducts
open scoped Pointwise
universe ur us um
variable {R : Type ur} [CommRing R] {S : Type us} [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

 theorem smul_top_le_of_map_dvd {p q : R} (h : algebraMap R S q ∣ algebraMap R S p) :
    p • (⊤ : Submodule R M) ≤ q • (⊤ : Submodule R M) := by
  intro z hz
  obtain ⟨w,_,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  obtain ⟨t,ht⟩ := h
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨t • w,Submodule.mem_top,?_⟩
  rw [← IsScalarTower.algebraMap_smul S q,← IsScalarTower.algebraMap_smul S p,
    smul_smul,← ht]

 theorem smul_top_eq_of_map_associated {p q : R}
    (h : Associated (algebraMap R S p) (algebraMap R S q)) :
    p • (⊤ : Submodule R M) = q • (⊤ : Submodule R M) :=
  le_antisymm (smul_top_le_of_map_dvd h.symm.dvd) (smul_top_le_of_map_dvd h.dvd)

variable {ι κ : Type*}

 theorem associated_prod_power (s : Finset ι) (a : ι → S) (p : S)
    (h : ∀ i ∈ s, Associated (a i) p) : Associated (∏ i ∈ s, a i) (p^s.card) := by
  simpa only [Finset.prod_const] using Associated.prod s a (fun _ => p) h

 theorem associated_prod_scale (s : Finset ι) (t : Finset κ) (a : ι → S) (b : κ → S)
    (p f : S) (k : ℕ) (ha : ∀ i ∈ s, Associated (a i) p)
    (hb : ∀ j ∈ t, Associated (b j) p) (hf : Associated f (p^k))
    (hcount : s.card=t.card+k) :
    Associated (∏ i ∈ s, a i) (f*∏ j ∈ t, b j) := by
  have hs := associated_prod_power s a p ha
  have ht := associated_prod_power t b p hb
  apply hs.trans
  have hpow : p^s.card=p^k*p^t.card := by rw [hcount,add_comm,pow_add]
  rw [hpow]
  exact (hf.mul_mul ht).symm

/-- The local embedded product images agree whenever the reduced labels are
associated and the actual later-edge count has the required difference. -/
 theorem product_image_scale (s : Finset ι) (t : Finset κ) (a : ι → R) (b : κ → R)
    (p : S) (f : R) (k : ℕ)
    (ha : ∀ i ∈ s, Associated (algebraMap R S (a i)) p)
    (hb : ∀ j ∈ t, Associated (algebraMap R S (b j)) p)
    (hf : Associated (algebraMap R S f) (p^k)) (hcount : s.card=t.card+k) :
    (∏ i ∈ s, a i) • (⊤ : Submodule R M) =
      f • ((∏ j ∈ t, b j) • (⊤ : Submodule R M)) := by
  rw [← mul_smul]
  apply smul_top_eq_of_map_associated (S := S)
  simpa only [map_prod,map_mul] using associated_prod_scale s t
    (fun i => algebraMap R S (a i)) (fun j => algebraMap R S (b j)) p
    (algebraMap R S f) k ha hb hf hcount

end KLInvariance.LocalProducts

end


section

namespace KLInvariance.TitsSpace
open Module BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem polynomialRoot_localized (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis a) =
      localizedLinear basis P a.val := rfl

 theorem polynomialRoot_reduced (P : Submodule ℝ (I → ℝ)) (a c : PositiveRoot M cs) :
    algebraMap (PlaneRing basis P) (LocalizedEdgeRing basis P a.val)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis c)) =
      localizedReduction basis P a.val c.val := rfl

 theorem planeRoot_outside {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    (planeRoot x a Q).val ∉ rootPlane a b := by
  intro h
  apply hQ
  rw [← planeRoot_plane x a Q]
  exact rootPlane_eq_of_mem a b a (planeRoot x a Q) hab
    (Submodule.subset_span (Set.mem_insert _ _)) h (planeRoot_ne x a Q).symm

 theorem reduced_planeRoot_other_isUnit {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    IsUnit (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val) := by
  have h := (linear_isUnit_iff basis (rootPlane a b) (planeRoot x a Q).val).mpr
    (planeRoot_outside hab Q hQ)
  exact h.map (algebraMap (PlaneRing basis (rootPlane a b))
    (LocalizedEdgeRing basis (rootPlane a b) a.val))

/-- The actual integral edge factor reduces, in each actual plane, to precisely
its plane weight. All other factors are proven units, not discarded formally. -/
 theorem edgeFactor_local_associated (x : W) (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Associated
      (algebraMap (PlaneRing basis (rootPlane a b)) (LocalizedEdgeRing basis (rootPlane a b) a.val)
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis (rootPlane a b)) (edgeFactorLift cs basis x a)))
      ((localizedReduction basis (rootPlane a b) a.val b.val)^((planeWeight x a (rootPlane a b)).toNat)) := by
  classical
  let p := localizedReduction basis (rootPlane a b) a.val b.val
  have hfactor (Q : (planeWeight x a).support) :
      Associated
        ((localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
        (if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) := by
    by_cases hQ : Q.val=rootPlane a b
    · rw [ite_eq_left hQ]
      have hc : (planeRoot x a Q).val ∈ rootPlane a b := by
        rw [← hQ,← planeRoot_plane x a Q]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h := localizedReduction_associated basis (rootPlane a b) a b (planeRoot x a Q)
        hc (planeRoot_ne x a Q)
      simpa only [hQ] using (Associated.pow_pow (M := LocalizedEdgeRing basis (rootPlane a b) a.val) h (n := (planeWeight x a Q.val).toNat))
    · rw [ite_eq_right hQ]
      exact associated_one_iff_isUnit.mpr ((reduced_planeRoot_other_isUnit basis hab Q hQ).pow _)
  have hprod := Associated.prod Finset.univ
    (fun Q : (planeWeight x a).support =>
      (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
    (fun Q => if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1)
    (fun Q _ => hfactor Q)
  have hp : (∏ Q : (planeWeight x a).support,
      if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) =
      p^((planeWeight x a (rootPlane a b)).toNat) := by
    rw [Fintype.prod_ite_eq_ite_exists _ (fun i j hi hj => Subtype.ext (hi.trans hj.symm))]
    by_cases hP : rootPlane a b ∈ (planeWeight x a).support
    · rw [ite_eq_left ⟨⟨rootPlane a b,hP⟩,rfl⟩]
    · have hz := Finsupp.notMem_support_iff.mp hP
      rw [hz,Int.toNat_zero,pow_zero]
      split_ifs <;> rfl
  rw [hp] at hprod
  simpa only [edgeFactorLift,map_prod,map_pow,polynomialRoot_reduced] using hprod

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetRoot_eq (e : B.CosetEdge a₀ b) :
    BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)=B.edgeRoot e.property := by
  rw [B.edgeRoot_coset hmin e.property]
  rfl

 theorem cosetLabel_eq_root (e : B.CosetEdge a₀ b) :
    B.cosetLabel basis a₀ b hmin e=localizedLinear basis P (B.edgeRoot e.property).val := by
  change algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialRoot cs basis (BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)))=_
  rw [B.cosetRoot_eq a₀ b hmin e]
  rfl

 def reducedCosetRoot (e : B.CosetEdge a₀ b) (β : PositiveRoot M cs) :
    PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e} :=
  algebraMap (PlaneRing basis P) _ (localizedLinear basis P β.val)

 theorem cosetLabel_reduction_associated (e f : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hplane : rootPlane (B.edgeRoot e.property) β=P)
    (hne : B.edgeRoot f.property ≠ B.edgeRoot e.property) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (B.cosetLabel basis a₀ b hmin f))
      (B.reducedCosetRoot basis a₀ b hmin e β) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e,B.cosetLabel_eq_root basis a₀ b hmin f]
  exact localizedReduction_associated basis P (B.edgeRoot e.property) β (B.edgeRoot f.property)
    (hplane.symm ▸ B.edgeRoot_plane f.property) hne

 theorem cosetFactor_reduction_associated (e : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hab : B.edgeRoot e.property ≠ β)
    (hplane : rootPlane (B.edgeRoot e.property) β=P) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
          (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))))
      ((B.reducedCosetRoot basis a₀ b hmin e β)^((planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat)) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e]
  have h := edgeFactor_local_associated basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) β hab
  rw [hplane] at h
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.BruhatGraph
open TitsSpace
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def upperSource (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩
 def upperTarget (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),(target cs 1 b e).property.2⟩
 def mappedEdgeRoot (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) :
     PositiveRoot M' cs' :=
   graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ (upperSource e hx) (upperTarget e hx)).mpr e.property)

end
end KLInvariance.BruhatGraph

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem exists_coset_edge {b : W} (e : Edge cs 1 b)
    (he : (BruhatGraph.root cs 1 b e).val ∈ P) :
    ∃ a₀, ∃ hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀),
      ∃ d : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin d=e := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P (source cs 1 b e).val
  have ht : label cs 1 b e ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs
      ⟨label cs 1 b e,label_isReflection cs 1 b e⟩)).mpr he
  let gg : planeSubgroup M cs P := ⟨g,hg⟩
  let hh : planeSubgroup M cs P := ⟨label cs 1 b e*g,(planeSubgroup M cs P).mul_mem ht hg⟩
  have hy : (hh:W)*a₀=(target cs 1 b e).val := by
    change (label cs 1 b e*g)*a₀=_
    rw [mul_assoc,← hx,label_mul_source]
  let x : B.CosetVertex a₀ b := ⟨gg,one_bruhat B.system gg,hx ▸ (source cs 1 b e).property.2⟩
  let y : B.CosetVertex a₀ b := ⟨hh,one_bruhat B.system hh,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hs : BruhatStep B.system gg hh := by
    apply (B.coset_step_iff hmin gg hh).mp
    rw [show (gg:W)*a₀=(source cs 1 b e).val from hx.symm,hy]
    exact e.property
  refine ⟨a₀,hmin,⟨(x,y),hs⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx.symm) (Subtype.ext hy)

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')

 theorem mappedCosetRoot_eq (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    B.mappedCosetRoot hmin φ e hx = mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin e) hx := rfl

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual transported finite-interval elementary matrix is the
second system's genuine R-tilde matrix. The input is only the unlabelled
order isomorphism; reflection edges are recovered by the checked general
Bruhat-graph reconstruction theorem. -/

end

end OAI
