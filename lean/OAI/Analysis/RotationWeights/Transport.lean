import OAI.Analysis.RotationWeights.Polar

namespace OAI

noncomputable section

namespace CircleTransport

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Op := H →L[ℂ] H

lemma commute_projection_of_reducing (P : Submodule ℂ H) [CompleteSpace P]
    (B : Op (H := H)) (hB : ∀ x ∈ P, B x ∈ P)
    (hs : ∀ x ∈ P, (star B) x ∈ P) : Commute P.starProjection B := by
  have ho (x : H) (hx : x∈Pᗮ) : B x∈Pᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hx _ (hs y hy)
  ext x
  change P.starProjection (B x) = B (P.starProjection x)
  have hx : x=P.starProjection x+(x-P.starProjection x) := by abel
  conv_lhs => rw [hx]
  rw [map_add,map_add,
    P.starProjection_mem_subspace_eq_self ⟨_,hB _ (P.starProjection_apply_mem x)⟩,
    P.starProjection_apply_eq_zero_iff.mpr (ho _ (P.sub_starProjection_mem_orthogonal x)),add_zero]

omit [CompleteSpace H] in
lemma invariant_closure (P : Submodule ℂ H) (B : Op (H := H))
    (hB : ∀ x∈P, B x∈P) : ∀ x∈P.topologicalClosure, B x∈P.topologicalClosure := by
  intro x hx
  apply closure_minimal (s := (P : Set H)) _
    ((Submodule.isClosed_topologicalClosure P).preimage B.continuous) hx
  intro y hy
  exact P.le_topologicalClosure (hB y hy)

lemma commutes_star_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    {A : Op (H := H)} (hA : ∀ B∈C, Commute A B) : ∀ B∈C, Commute (star A) B := by
  intro B hB
  have h := (hA (star B) (star_mem hB)).star_star
  simpa using h


lemma projection_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    (P : Submodule ℂ H) [CompleteSpace P]
    (hP : ∀ B∈C, ∀ x∈P, B x∈P) : ∀ B∈C, Commute P.starProjection B := by
  intro B hB
  exact commute_projection_of_reducing P B (hP B hB) (hP (star B) (star_mem hB))

lemma polar_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    {A : Op (H := H)} (hA : ∀ B∈C, Commute A B) :
    ∀ B∈C, Commute (CirclePolar.polar A) B := by
  intro B hB
  exact CirclePolar.commute_polar (hA B hB) (commutes_star_centralizer C hA B hB)

lemma exists_cutoff_intersection (C : StarSubalgebra ℂ (Op (H := H)))
    (v : H) (htrace : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → ‖star A v‖=‖A v‖)
    (P : Submodule ℂ H) [CompleteSpace P] (hP : ∀ B∈C, Commute P.starProjection B)
    (hPv : P.starProjection v≠0) (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hE : ∀ n, ∀ B∈C, Commute (E n).starProjection B)
    (hlim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v)) :
    ∃ n, ∃ x : H, x∈P ∧ x∈E n ∧ x≠0 := by
  have ht : Filter.Tendsto (fun n => ‖(E n)ᗮ.starProjection v‖) Filter.atTop (nhds 0) := by
    simp_rw [Submodule.starProjection_orthogonal,sub_apply,ContinuousLinearMap.id_apply]
    simpa using ((tendsto_const_nhds (x := v)).sub hlim).norm
  have he : ∀ᶠ n in Filter.atTop, ‖(E n)ᗮ.starProjection v‖ < ‖P.starProjection v‖ :=
    (tendsto_order.1 ht).2 _ (norm_pos_iff.mpr hPv)
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨n,CirclePolar.exists_intersection_of_norm_lt P (E n) v ?_ hn⟩
  apply htrace
  apply polar_mem_centralizer C
  intro B hB
  apply Commute.mul_left _ (hP B hB)
  rw [Submodule.starProjection_orthogonal]
  exact (Commute.one_left B).sub_left (hE n B hB)

def transportedRange (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Submodule ℂ H :=
  ((P.comap D.subtype).map A).topologicalClosure

instance (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H) : CompleteSpace (transportedRange D P A) :=
  inferInstanceAs (CompleteSpace ((P.comap D.subtype).map A).topologicalClosure)

omit [CompleteSpace H] in
lemma transportedRange_invariant (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (T S : Op (H := H)) (hT : ∀ x∈P, T x∈P) (hD : ∀ x∈D, T x∈D)
    (hAS : ∀ x : D, A ⟨T x,hD x x.property⟩ = S (A x)) :
    ∀ x∈transportedRange D P A, S x∈transportedRange D P A := by
  apply invariant_closure
  rintro y ⟨x,hx,rfl⟩
  refine ⟨⟨T x,hD x x.property⟩,hT x hx,?_⟩
  exact hAS x

lemma transportedRange_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hP : ∀ B∈C, ∀ x∈P, B x∈P)
    (hD : ∀ B∈C, ∀ x∈D, B x∈D)
    (hA : ∀ B, ∀ hB : B∈C, ∀ x : D, A ⟨B x,hD B hB x x.property⟩ = B (A x)) :
    ∀ B∈C, Commute (transportedRange D P A).starProjection B := by
  apply projection_mem_centralizer
  intro B hB
  exact transportedRange_invariant D P A B B (hP B hB) (hD B hB) (hA B hB)

omit [CompleteSpace H] in
lemma transportedRange_ne_bot (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hA : Function.Injective A) (E : Submodule ℂ H) (hE : E≤D)
    (x : H) (hxP : x∈P) (hxE : x∈E) (hx0 : x≠0) : transportedRange D P A ≠ ⊥ := by
  let z : D := ⟨x,hE hxE⟩
  have hz : A z ∈ transportedRange D P A :=
    Submodule.le_topologicalClosure _ ⟨z,hxP,rfl⟩
  intro hh
  rw [hh,Submodule.mem_bot] at hz
  have : z=0 := hA (by simpa using hz)
  exact hx0 (congrArg Subtype.val this)

omit [CompleteSpace H] in
lemma transportedRange_ne_top (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hsym : ∀ x y : D, inner ℂ (A x) (y : H) = inner ℂ (x : H) (A y))
    (η : H) (hη : η∈Pᗮ) (hη0 : η≠0) (hηA : η∈LinearMap.range A) :
    transportedRange D P A ≠ ⊤ := by
  obtain ⟨χ,hχ⟩ := hηA
  have hχ0 : (χ : H)≠0 := by
    intro h
    have : χ=0 := Subtype.ext h
    exact hη0 (hχ.symm.trans (by rw [this,map_zero]))
  have horth : (χ : H)∈(transportedRange D P A)ᗮ := by
    rw [transportedRange,Submodule.orthogonal_closure]
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro y ⟨x,hx,rfl⟩
    rw [hsym,hχ]
    exact (Submodule.mem_orthogonal _ _).mp hη _ hx
  intro hh
  rw [hh,Submodule.top_orthogonal_eq_bot,Submodule.mem_bot] at horth
  exact hχ0 horth


omit [CompleteSpace H] in
lemma projection_ne_zero_of_ne_bot (P : Submodule ℂ H) [CompleteSpace P] (hP : P≠⊥) :
    P.starProjection≠0 := by
  intro hh
  apply hP
  have h := Submodule.range_starProjection P
  rw [hh] at h
  simpa using h.symm

omit [CompleteSpace H] in
lemma projection_ne_one_of_ne_top (P : Submodule ℂ H) [CompleteSpace P] (hP : P≠⊤) :
    P.starProjection≠1 := by
  intro hh
  apply hP
  apply top_unique
  intro x _
  rw [← Submodule.starProjection_eq_self_iff,hh]
  rfl

omit [CompleteSpace H] in
lemma invariant_projection (P : Submodule ℂ H) [CompleteSpace P] (S : Op (H := H))
    (hS : ∀ x∈P, S x∈P) : (1-P.starProjection)*S*P.starProjection=0 := by
  ext x
  change S (P.starProjection x)-P.starProjection (S (P.starProjection x))=0
  exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr (hS _ (P.starProjection_apply_mem x))).symm

theorem affiliated_transport (C : StarSubalgebra ℂ (Op (H := H))) (v : H)
    (htrace : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → ‖star A v‖=‖A v‖)
    (hfaith : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → A v=0 → A=0)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hAinj : Function.Injective A)
    (hsym : ∀ x y : D, inner ℂ (A x) (y : H)=inner ℂ (x : H) (A y))
    (hD : ∀ B∈C, ∀ x∈D, B x∈D)
    (hA : ∀ B, ∀ hB : B∈C, ∀ x : D, A ⟨B x,hD B hB x x.property⟩=B (A x))
    (E F : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)] [∀ n, CompleteSpace (F n)]
    (hE : ∀ n, ∀ B∈C, Commute (E n).starProjection B)
    (hF : ∀ n, ∀ B∈C, Commute (F n).starProjection B)
    (hED : ∀ n, E n≤D) (hFA : ∀ n, F n≤LinearMap.range A)
    (hElim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v))
    (hFlim : Filter.Tendsto (fun n => (F n).starProjection v) Filter.atTop (nhds v))
    (P : Submodule ℂ H) [CompleteSpace P] (hPC : ∀ B∈C, Commute P.starProjection B)
    (hP0 : P≠⊥) (hP1 : P≠⊤)
    (T S : Op (H := H)) (hTP : ∀ x∈P, T x∈P) (hTD : ∀ x∈D, T x∈D)
    (hAS : ∀ x : D, A ⟨T x,hTD x x.property⟩=S (A x)) :
    ∃ q : Op (H := H), IsStarProjection q ∧ (∀ B∈C, Commute q B) ∧
      q≠0 ∧ q≠1 ∧ (1-q)*S*q=0 := by
  have hP (B : Op (H := H)) (hB : B∈C) (x : H) (hx : x∈P) : B x∈P := by
    rw [← Submodule.starProjection_eq_self_iff]
    have hh := DFunLike.congr_fun (hPC B hB).eq x
    change P.starProjection (B x)=B (P.starProjection x) at hh
    rw [hh,Submodule.starProjection_eq_self_iff.mpr hx]
  have hPv : P.starProjection v≠0 := by
    intro hh
    exact projection_ne_zero_of_ne_bot P hP0 (hfaith _ hPC hh)
  have hQc : ∀ B∈C, Commute Pᗮ.starProjection B := by
    intro B hB
    rw [Submodule.starProjection_orthogonal]
    exact (Commute.one_left B).sub_left (hPC B hB)
  have hQ0 : Pᗮ ≠ ⊥ := by
    intro hh
    have hh' := congrArg (fun Q : Submodule ℂ H => Qᗮ) hh
    rw [Submodule.orthogonal_orthogonal,Submodule.bot_orthogonal_eq_top] at hh'
    exact hP1 hh'
  have hQv : Pᗮ.starProjection v≠0 := by
    intro hh
    exact projection_ne_zero_of_ne_bot Pᗮ hQ0 (hfaith _ hQc hh)
  obtain ⟨n,x,hxP,hxE,hx0⟩ := exists_cutoff_intersection C v htrace P hPC hPv E hE hElim
  obtain ⟨m,η,hηP,hηF,hη0⟩ := exists_cutoff_intersection C v htrace Pᗮ hQc hQv F hF hFlim
  let W := transportedRange D P A
  refine ⟨W.starProjection,?_,transportedRange_mem_centralizer C D P A hP hD hA,
    projection_ne_zero_of_ne_bot W (transportedRange_ne_bot D P A hAinj (E n) (hED n) x hxP hxE hx0),
    projection_ne_one_of_ne_top W (transportedRange_ne_top D P A hsym η hηP hη0 (hFA m hηF)),
    invariant_projection W S (transportedRange_invariant D P A T S hTP hTD hAS)⟩
  exact isStarProjection_starProjection
end
open ContinuousLinearMap
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fractionMap (b c : Op (H:=H)) (hb : Function.Injective b) :
    LinearMap.range b.toLinearMap →ₗ[ℂ] H :=
  c.toLinearMap.comp (LinearEquiv.ofInjective b.toLinearMap hb).symm.toLinearMap
omit [CompleteSpace H] in
lemma fractionMap_apply (b c : Op (H:=H)) (hb : Function.Injective b) (x : H) :
    fractionMap b c hb ⟨b x,⟨x,rfl⟩⟩=c x := by
  change c ((LinearEquiv.ofInjective b.toLinearMap hb).symm ((LinearEquiv.ofInjective b.toLinearMap hb) x))=c x
  rw [LinearEquiv.symm_apply_apply]
omit [CompleteSpace H] in
lemma fractionMap_injective (b c : Op (H:=H)) (hb : Function.Injective b) (hc : Function.Injective c) :
    Function.Injective (fractionMap b c hb) := hc.comp (LinearEquiv.ofInjective b.toLinearMap hb).symm.injective
omit [CompleteSpace H] in
lemma fractionMap_range (b c : Op (H:=H)) (hb : Function.Injective b) :
    LinearMap.range (fractionMap b c hb)=LinearMap.range c.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨⟨b x,⟨x,rfl⟩⟩,fractionMap_apply b c hb x⟩
lemma fractionMap_symmetric (b c : Op (H:=H)) (hb : Function.Injective b)
    (hsb : IsSelfAdjoint b) (hsc : IsSelfAdjoint c) (hbc : Commute b c)
    (x y : LinearMap.range b.toLinearMap) :
    inner ℂ (fractionMap b c hb x) (y:H)=inner ℂ (x:H) (fractionMap b c hb y) := by
  obtain ⟨u,hu⟩ := x.property
  obtain ⟨v,hv⟩ := y.property
  have hx : x=⟨b u,⟨u,rfl⟩⟩ := Subtype.ext hu.symm
  have hy : y=⟨b v,⟨v,rfl⟩⟩ := Subtype.ext hv.symm
  rw [hx,hy,fractionMap_apply,fractionMap_apply]
  have hb' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsb
  have hc' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsc
  change inner ℂ (c u) (b v)=inner ℂ (b u) (c v)
  change inner ℂ (c.toLinearMap u) (b.toLinearMap v)=inner ℂ (b.toLinearMap u) (c.toLinearMap v)
  rw [hc',hb']
  exact congrArg (fun z => inner ℂ u z) (DFunLike.congr_fun hbc.eq v).symm

omit [CompleteSpace H] in
lemma fraction_domain_map (b T L : Op (H:=H)) (h : T*b=b*L) :
    ∀ x∈LinearMap.range b.toLinearMap,T x∈LinearMap.range b.toLinearMap := by
  rintro x ⟨y,rfl⟩
  exact ⟨L y,(DFunLike.congr_fun h y).symm⟩
omit [CompleteSpace H] in
lemma fractionMap_intertwine (b c T S L : Op (H:=H)) (hb : Function.Injective b)
    (hT : T*b=b*L) (hS : S*c=c*L) (x : LinearMap.range b.toLinearMap) :
    fractionMap b c hb ⟨T x,fraction_domain_map b T L hT x x.property⟩=S (fractionMap b c hb x) := by
  obtain ⟨y,hy⟩ := x.property
  have hx : x=⟨b y,⟨y,rfl⟩⟩ := Subtype.ext hy.symm
  subst x
  rw [fractionMap_apply]
  have he : (⟨T (b y),fraction_domain_map b T L hT _ ⟨y,rfl⟩⟩ : LinearMap.range b.toLinearMap)=⟨b (L y),⟨L y,rfl⟩⟩ :=
    Subtype.ext (DFunLike.congr_fun hT y)
  rw [he,fractionMap_apply]
  exact (DFunLike.congr_fun hS y).symm

theorem bounded_fraction_transport (C : StarSubalgebra ℂ (Op (H:=H))) (v : H)
    (htrace : ∀ A : Op (H:=H),(∀ B∈C,Commute A B)→‖star A v‖=‖A v‖)
    (hfaith : ∀ A : Op (H:=H),(∀ B∈C,Commute A B)→A v=0→A=0)
    (b c : Op (H:=H)) (hb : Function.Injective b) (hc : Function.Injective c)
    (hsb : IsSelfAdjoint b) (hsc : IsSelfAdjoint c) (hbc : Commute b c)
    (hbC : ∀ B∈C,Commute b B) (hcC : ∀ B∈C,Commute c B)
    (E F : ℕ → Submodule ℂ H) [∀ n,CompleteSpace (E n)] [∀ n,CompleteSpace (F n)]
    (hE : ∀ n,∀ B∈C,Commute (E n).starProjection B)
    (hF : ∀ n,∀ B∈C,Commute (F n).starProjection B)
    (hEb : ∀ n,E n≤LinearMap.range b.toLinearMap)
    (hFc : ∀ n,F n≤LinearMap.range c.toLinearMap)
    (hElim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v))
    (hFlim : Filter.Tendsto (fun n => (F n).starProjection v) Filter.atTop (nhds v))
    (P : Submodule ℂ H) [CompleteSpace P] (hPC : ∀ B∈C,Commute P.starProjection B)
    (hP0 : P≠⊥) (hP1 : P≠⊤)
    (T S L : Op (H:=H)) (hTP : ∀ x∈P,T x∈P) (hT : T*b=b*L) (hS : S*c=c*L) :
    ∃ q : Op (H:=H),IsStarProjection q ∧ (∀ B∈C,Commute q B) ∧ q≠0 ∧ q≠1 ∧ (1-q)*S*q=0 := by
  apply affiliated_transport C v htrace hfaith (LinearMap.range b.toLinearMap) (fractionMap b c hb)
    (fractionMap_injective b c hb hc) (fractionMap_symmetric b c hb hsb hsc hbc)
    (fun B hB => fraction_domain_map b B B (hbC B hB).symm.eq)
    (fun B hB x => fractionMap_intertwine b c B B B hb (hbC B hB).symm.eq (hcC B hB).symm.eq x)
    E F hE hF hEb _ hElim hFlim P hPC hP0 hP1 T S hTP
    (fraction_domain_map b T L hT) (fractionMap_intertwine b c T S L hb hT hS)
  intro n
  rw [fractionMap_range]
  exact hFc n


end CircleTransport

end

end OAI
