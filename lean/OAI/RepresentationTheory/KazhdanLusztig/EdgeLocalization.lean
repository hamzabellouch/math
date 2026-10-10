import OAI.RepresentationTheory.KazhdanLusztig.PlaneLocalization

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/

section

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 def transportedEdge (e : Edge cs u b) : AdaptedDyer.Edge cs' :=
  ⟨((φ (source cs u b e)).val,(φ (target cs u b e)).val),
    (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mpr e.property⟩

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_injective : Function.Injective (transportedEdge φ) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Prod.ext (φ.injective (Subtype.ext (congrArg Prod.fst hh)))
    (φ.injective (Subtype.ext (congrArg Prod.snd hh)))

 def transportedScore (e : Edge cs u b) : ℝ ×ₗ ℝ :=
  lexEdgeScore (geometricFunctional (M := M') (cs := cs')) (transportedEdge φ e)

 /-- Decreasing list, in the convention for the outermost-first matrix
 product. Its reverse is chronological increasing reflection order. -/
 def transportedSchedule : List (Edge cs u b) := by
  letI := Fintype.ofFinite (Edge cs u b)
  exact sortedSchedule Finset.univ (transportedScore φ)

omit [Fintype I] in
 theorem transportedSchedule_nodup : (transportedSchedule φ).Nodup := by
  unfold transportedSchedule
  exact sortedSchedule_nodup _ _

omit [Fintype I] in
 theorem transportedSchedule_full (e : Edge cs u b) : e ∈ transportedSchedule φ := by
  let := Fintype.ofFinite (Edge cs u b)
  unfold transportedSchedule
  exact (mem_sortedSchedule _ _ _).mpr (Finset.mem_univ _)

omit [Fintype I] in
 theorem transportedSchedule_pairwise : (transportedSchedule φ).Pairwise
     (fun e f => transportedScore φ f ≤ transportedScore φ e) := by
  unfold transportedSchedule
  exact sortedSchedule_pairwise _ _

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_lift (e : AdaptedDyer.Edge cs')
    (hu : BruhatLE cs' u' (AdaptedDyer.source cs' e))
    (hb : BruhatLE cs' (AdaptedDyer.target cs' e) b') : ∃ f, transportedEdge φ f=e := by
  let x : Interval cs' u' b' := ⟨AdaptedDyer.source cs' e,hu,
    (show BruhatLE cs' (AdaptedDyer.source cs' e) (AdaptedDyer.target cs' e) from
      .single e.property).trans hb⟩
  let y : Interval cs' u' b' := ⟨AdaptedDyer.target cs' e,
    hu.trans (.single e.property),hb⟩
  let f : Edge cs u b := ⟨(φ.symm x,φ.symm y),
    (intervalIso_bruhatStep_iff_general cs' cs φ.symm x y).mpr e.property⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  change ((φ (φ.symm x)).val,(φ (φ.symm y)).val)=e.val
  rw [φ.apply_symm_apply,φ.apply_symm_apply]
  rfl

omit [Fintype I] in
 theorem transported_dispatch_entry {R : Type*} [Semiring R] (T : R)
    (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T (fun z => if z=y then 1 else 0)
      (transportedSchedule φ) x =
    WallDyer.entry (cs := cs') T (geometricFunctional (M := M') (cs := cs'))
      b' (φ x).val (φ y).val := by
  have hsource {z w : W'} {p : List (AdaptedDyer.Edge cs')}
      (hp : IsPath (AdaptedDyer.source cs') (AdaptedDyer.target cs') z w p) :
      ∀ e ∈ p, BruhatLE cs' z (AdaptedDyer.source cs' e) := by
    induction p generalizing z with
    | nil => simp
    | cons e p ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hp.1 ▸ bruhat_refl cs' z
      · rw [← hp.1]
        exact (show BruhatLE cs' (AdaptedDyer.source cs' e)
          (AdaptedDyer.target cs' e) from .single e.property).trans (ih hp.2 f hf)
  symm
  apply dispatch_entry_graph_embedding (AdaptedDyer.source cs') (AdaptedDyer.target cs')
    (source cs u b) (target cs u b) T
    (lexEdgeScore (geometricFunctional (M := M') (cs := cs')))
    (lexEdgeScore_ties _) (fun z : Interval cs u b => (φ z).val)
    (fun _ _ h => φ.injective (Subtype.ext h)) (transportedEdge φ)
    (transportedEdge_injective φ) (fun _ => rfl) (fun _ => rfl)
    (WallDyer.schedule (geometricFunctional (M := M') (cs := cs')) b')
    (transportedSchedule φ) (sortedSchedule_nodup _ _)
    (transportedSchedule_nodup φ) (sortedSchedule_pairwise _ _)
    (transportedSchedule_pairwise φ) (transportedSchedule_full φ)
  · intro e
    exact (mem_sortedSchedule _ _ _).mpr ((AdaptedDyer.mem_edgeFinset cs' b' _).mpr
      (φ (target cs u b e)).property.2)
  · intro r hr e he
    have hp := ((mem_subpaths _ _ _ _ _ r).mp hr).2
    exact transportedEdge_lift φ e ((φ x).property.1.trans (hsource hp e he))
      ((AdaptedDyer.path_targets_le cs' hp e he).trans (φ y).property.2)

omit [Fintype I] in

 theorem transported_entry_eq_rTilde (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) (Polynomial.X : Polynomial ℤ)
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Hecke.rTilde cs' (φ x).val (φ y).val := by
  rw [transported_dispatch_entry]
  exact WallDyer.geometric_entry_eq_rTilde b' (φ x).val (φ y).val
    (φ x).property.2 (φ y).property.2

end
end KLInvariance.BruhatGraph

end


section

/-! Actual transported numerical R-tilde matrix and its genuine KL reciprocal
vector. No sheaf or desired invariance conclusion is assumed. -/
namespace KLInvariance.SchedulePaths
universe u v w w'
variable {V : Type u} {E : Type v} {R : Type w} {S : Type w'}
  [Semiring R] [Semiring S] (source target : E → V)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem dispatch_map (f : R →+* S) (T : R) (v : V → R) (p : List E) (x : V) :
    f (dispatch source target T v p x) =
      dispatch source target (f T) (fun z => f (v z)) p x := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,step,map_add]
    split_ifs <;> simp only [map_mul,map_zero,ih]

end
end KLInvariance.SchedulePaths

namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (u b : W) (x : Interval cs u b) :
    scaledKL cs t x.val b = ∑ᶠ z : Interval cs u b,
      Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val) *
        scaledKL cs t⁻¹ z.val b := by
  classical
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs x.val b
  let := Fintype.ofFinite (Interval cs x.val b)
  rw [scaledKL_reciprocity cs t ht x.val b x.property.2,
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  let f : W → C := fun z => Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t)
    (Hecke.rTilde cs x.val z) * scaledKL cs t⁻¹ z b
  have hs (a : W) [Fintype (Interval cs a b)] :
      (∑ z : Interval cs a b, f z.val) =
        ∑ z ∈ (lowerFinset cs b).filter (fun z => BruhatLE cs a z), f z := by
    exact (Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs a b)))
      ((lowerFinset cs b).filter (fun z => BruhatLE cs a z))
      (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm) f).symm
  change (∑ z : Interval cs x.val b, f z.val) = ∑ z : Interval cs u b, f z.val
  rw [hs,hs]
  apply Finset.sum_subset
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz,hxz⟩
    exact Finset.mem_filter.mpr ⟨hz,x.property.1.trans hxz⟩
  · intro z hz hn
    have hxz : ¬ BruhatLE cs x.val z := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,h⟩)
    dsimp [f]
    rw [Hecke.rTilde_zero cs _ _ hxz,Polynomial.eval₂_zero,zero_mul]

end
end KLInvariance

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem transported_entry_eval {C : Type*} [CommSemiring C] (T : C)
    (x y : Interval cs u b) (f : ℤ →+* C) :
    dispatch (source cs u b) (target cs u b) T
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) := by
  rw [← transported_entry_eq_rTilde φ x y]
  have h := dispatch_map (source cs u b) (target cs u b) (Polynomial.eval₂RingHom f T)
    Polynomial.X (fun z : Interval cs u b => if z=y then 1 else 0) (transportedSchedule φ) x
  simpa using h.symm

 theorem transported_dispatch_matrix {C : Type*} [CommSemiring C] (T : C)
    (f : ℤ →+* C) (v : Interval cs u b → C) (x : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T v (transportedSchedule φ) x =
      ∑ᶠ y : Interval cs u b,
        Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) * v y := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  rw [dispatch_eq_sum_entries,finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y)
    (transported_entry_eval φ T x y f))

 theorem transported_reciprocal_vector {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (x : Interval cs u b) :
    scaledKL cs' t (φ x).val b' =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs' t⁻¹ (φ y).val b') (transportedSchedule φ) x := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs' u' b'
  let := Fintype.ofFinite (Interval cs' u' b')
  rw [transported_dispatch_matrix φ _ (Int.castRingHom C),
    scaledKL_reciprocity_upper cs' t ht u' b' (φ x),
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  exact (φ.toEquiv.sum_comp _).symm

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (C : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 theorem boundarySheaf_gradedIso :
    Nonempty (GradedSheaf.Iso (boundarySheaf cs u b basis hub).sheaf C.sheaf) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact BoundarySheaf.exists_gradedIso (polynomialGrading_zero ℝ σ)
    (boundarySheaf cs u b basis hub) C (fun x => x.property.2)

 theorem stalkCharacter_eq_character (x : Interval cs u b) :
    let _ := C.free x
    stalkCharacter cs u b basis hub x =
      Graded.character (σ := σ) (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg := by
  let _ := C.free x
  let B := boundarySheaf cs u b basis hub
  let _ := B.free x
  obtain ⟨j⟩ := boundarySheaf_gradedIso cs u b basis hub C
  exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)

end
end KLInvariance.BruhatGraph

end


section

/-! Faithful upper-interval restriction of the actual minimal boundary sheaf.
The bottom is arbitrary. No roots or labels are supplied by the interval iso. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
noncomputable section

 def upperInclusion : GraphMap (graph cs u b) (graph cs 1 b) where
  vertex x := ⟨x.val,one_bruhat cs x.val,x.property.2⟩
  edge e := ⟨(⟨(source cs u b e).val,one_bruhat cs _,(source cs u b e).property.2⟩,
    ⟨(target cs u b e).val,one_bruhat cs _,(target cs u b e).property.2⟩),e.property⟩
  source _ := rfl
  target _ := rfl

omit [Fintype I] in
 theorem upperInclusion_injective : Function.Injective (upperInclusion cs u b).vertex := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Interval cs 1 b => z.val) h)

omit [Fintype I] in
 theorem upperInclusion_outgoing (e : Edge cs 1 b) (x : Interval cs u b)
    (hx : (upperInclusion cs u b).vertex x = source cs 1 b e) :
    ∃ a, (upperInclusion cs u b).edge a=e ∧ source cs u b a=x := by
  have hxval := congrArg Subtype.val hx
  let y : Interval cs u b := ⟨(target cs 1 b e).val,
    bruhat_trans cs x.property.1 (hxval.symm ▸ Relation.ReflTransGen.single e.property),
    (target cs 1 b e).property.2⟩
  let a : Edge cs u b := ⟨(x,y),hxval.symm ▸ e.property⟩
  refine ⟨a,?_,rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · rfl

variable {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)

 def restrictBoundary : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  B.pullback (upperInclusion cs u b) (upperInclusion_injective cs u b)
    (upperInclusion_outgoing cs u b) ⟨b,hub,bruhat_refl cs b⟩ rfl

 theorem stalkCharacter_upperRestriction (x : Interval cs u b) :
    let _ := B.free ((upperInclusion cs u b).vertex x)
    stalkCharacter cs u b basis hub x =
      Graded.character (σ := σ) (B.sheaf.vertex ((upperInclusion cs u b).vertex x)).piece
        (B.sheaf.vertex ((upperInclusion cs u b).vertex x)).nonneg :=
  stalkCharacter_eq_character cs u b basis hub (restrictBoundary cs u b basis hub B) x

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance scaledInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

 theorem stalkCharacter_natDegree_le (x : Interval cs 1 b) :
    (stalkCharacter cs 1 b basis (one_bruhat cs b) x).natDegree≤rankDifference cs x.val b := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free x
  let c := (exists_nonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg).some
  rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) B x,
    character_eq (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using stalkBasis_degree_le cs b basis x c i

 def scaledStalk {C : Type*} [Field C] (t : C) (x : Interval cs 1 b) : C :=
  t^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) (t^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)

 theorem scaledStalk_reciprocity_inverse {C : Type*} [Field C]
    (v : C) (hv : v≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis v⁻¹ x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis v z := by
  classical
  have hrec := stalkCharacter_reciprocity cs basis b x
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ (stalkCharacter_natDegree_le cs b basis x)] at heval
  simp only [eval₂_finsetSum,eval₂_mul] at heval
  have hq : (q : C)=v^2 := rfl
  have hqi : (↑q⁻¹ : C)=(v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  have heq := congrArg (fun a : C => v^((cs.length x.val : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x.val b : ℤ)=(cs.length b : ℤ)-cs.length x.val := by
    simp [rankDifference,Int.ofNat_sub (length_le_of_bruhat cs x.property.2)]
  have hscale : v^((cs.length x.val : ℤ)-cs.length b)*(v^2)^(rankDifference cs x.val b)=
      (v⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [←pow_mul,←zpow_natCast,←zpow_add₀ hv,inv_zpow,←zpow_neg]
    congr 1
    push_cast
    omega
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) ((v⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=_
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  have hr : OrdinaryR.polynomial cs x.val z.val=rPolynomial cs x.val z.val :=
    (rPolynomial_eq_constructed cs x.val z.val).symm
  rw [hr,rPolynomial_normalization cs v hv]
  unfold scaledStalk
  calc
    _ = (v^((cs.length x.val : ℤ)-cs.length b)*v^((cs.length z.val : ℤ)-cs.length x.val))*
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        eval₂ (Int.castRingHom C) (v^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) z) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x.val : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x.val)=(cs.length z.val : ℤ)-cs.length b by ring]
      ring

 theorem scaledStalk_reciprocity {C : Type*} [Field C]
    (t : C) (ht : t≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis t x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis t⁻¹ z := by
  simpa only [inv_inv] using scaledStalk_reciprocity_inverse cs b basis t⁻¹ (inv_ne_zero ht) x

 theorem scaledStalk_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t≠0) (a : W) (x : Interval cs a b) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)=
      ∑ᶠ z : Interval cs a b,
        eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
          scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z) := by
  classical
  let := interval_finite cs a b
  let := Fintype.ofFinite (Interval cs a b)
  rw [scaledStalk_reciprocity cs b basis t ht, finsum_eq_sum_of_fintype]
  let e : {z : Interval cs 1 b // BruhatLE cs a z.val} ≃ Interval cs a b :=
    ⟨fun z => ⟨z.val.val,z.property,z.val.property.2⟩,
      fun z => ⟨(upperInclusion cs a b).vertex z,z.property.1⟩,fun _ => rfl,fun _ => rfl⟩
  let g (z : Interval cs 1 b) :=
    eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*scaledStalk cs b basis t⁻¹ z
  change (∑ z : Interval cs 1 b, g z)=_
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : Interval cs 1 b => BruhatLE cs a z.val),g z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have hnot : ¬BruhatLE cs x.val z.val := by
        intro hxz
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bruhat_trans cs x.property.1 hxz⟩)
      simp [g,Hecke.rTilde_zero cs x.val z.val hnot]
    _ = ∑ z : {z : Interval cs 1 b // BruhatLE cs a z.val}, g z.val :=
      Finset.sum_subtype _ (by simp) g
    _ = _ := Equiv.sum_comp e (fun z =>
      eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z))

end
end KLInvariance.BruhatGraph

end


section

/-! A specified morphism between honest minimal free covers is an isomorphism
if it covers the identity. This will recognize the canonical restricted word
form, not merely an arbitrary choice of self-duality. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {T : ModuleData.{uk,ua,um} 𝓐}

include hneg hzero in
 theorem MinimalCover.hom_bijective (C D : MinimalCover T)
    (f : Hom C.source D.source) (hf : D.hom.map.comp f.map=C.hom.map) :
    Function.Bijective f.map := by
  let := C.free
  let := D.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective D.hom
  have hfa (v : C.source) : D.hom.map (f.map v)=C.hom.map v := LinearMap.congr_fun hf v
  have hga (v : D.source) : C.hom.map (g.map v)=D.hom.map v := LinearMap.congr_fun hg v
  have hgf : Function.Bijective (g.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply C.minimal
    change C.hom.map (m-g.map (f.map m))=0
    rw [map_sub,hga,hfa,sub_self]
  have hfg : Function.Bijective (f.comp g).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply D.minimal
    change D.hom.map (m-f.map (g.map m))=0
    rw [map_sub,hfa,hga,sub_self]
  exact ⟨Function.Injective.of_comp hgf.1,Function.Surjective.of_comp hfg.2⟩

end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem stalk_hom_bijective
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x)
    (f₀ : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hf₀ : ∀ v, j.boundary (B.forget.stalkMap x v) =
      C.forget.stalkMap x (f₀.map v)) : Function.Bijective f₀.map := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  apply F.hom_bijective hneg hzero D f₀
  apply LinearMap.ext
  intro v
  exact Subtype.ext (hf₀ v).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.edge_bijective_of_vertex (f : Hom B C) (α : E → A)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  let v := LinearEquiv.ofBijective (f.vertex (G.target e)).map hv
  let j := QuotientEdge.iso (B.upper e).map (C.upper e).map
    (hB e).1 (hC e).1 v (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v)
  have he : (f.edge e).map=j.toLinearMap := by
    apply LinearMap.ext
    intro m
    obtain ⟨m,rfl⟩ := (hB e).1 m
    rw [f.upper]
    exact (QuotientEdge.iso_apply (B.upper e).map (C.upper e).map
      (hB e).1 (hC e).1 v
      (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v) m).symm
  rw [he]
  exact j.bijective

 def Hom.isoOfBijective (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Iso B C where
  vertex x := LinearEquiv.ofBijective (f.vertex x).map (hv x)
  edge e := LinearEquiv.ofBijective (f.edge e).map (he e)
  lower := f.lower
  upper := f.upper
  vertex_graded x := (f.vertex x).graded
  edge_graded e := (f.edge e).graded

 def Hom.aboveIso (f : Hom B C) (x : V)
    (hv : ∀ y, x<y → Function.Bijective (f.vertex y).map)
    (he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map) :
    Sheaf.AboveIso B.forget C.forget x where
  vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (hv y hy)
  edge e he' := LinearEquiv.ofBijective (f.edge e).map (he e he')
  lower e _ := f.lower e
  upper e _ := f.upper e

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Invertibility detected at the top of the actual normalized minimal-boundary
sheaf. This is stronger than uniqueness of its isomorphism class. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b)
noncomputable section

 include hzero in
 theorem hom_vertex_bijective (f : GradedSheaf.Hom B.sheaf C.sheaf)
    (hb : Function.Bijective (f.vertex b).map) (x : V) :
    Function.Bijective (f.vertex x).map := by
  classical
  refine wellFounded_gt.induction (C := fun y => Function.Bijective (f.vertex y).map) x ?_
  intro x ih
  by_cases hx : x=b
  · subst x
    exact hb
  have he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map :=
    fun e h => f.edge_bijective_of_vertex α B.quotient C.quotient e (ih _ h)
  let j := f.aboveIso x ih he
  apply j.stalk_hom_bijective hneg hzero
    (fun e h n v hv => (f.edge e).graded n v hv)
    (B.free x) (C.free x) B.flabby.flabby B.generated C.flabby.flabby C.generated
    (B.minimal x hx) (C.minimal x hx) (f.vertex x)
  intro v
  funext e
  change (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)=
    C.sheaf.forget.stalkMap x ((f.vertex x).map v) e
  rcases e with ⟨e,he⟩
  subst x
  exact f.lower e v

 def homIso (f : GradedSheaf.Hom B.sheaf C.sheaf)
    (hb : Function.Bijective (f.vertex b).map) : GradedSheaf.Iso B.sheaf C.sheaf :=
  f.isoOfBijective (hom_vertex_bijective hzero B C f hb)
    (fun e => f.edge_bijective_of_vertex α B.quotient C.quotient e
      (hom_vertex_bijective hzero B C f hb _))

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Iso.hom (j : Iso B C) : Hom B C where
  vertex x := ⟨(j.vertex x).toLinearMap,j.vertex_graded x⟩
  edge e := ⟨(j.edge e).toLinearMap,j.edge_graded e⟩
  lower := j.lower
  upper := j.upper

 def Iso.invHom (j : Iso B C) : Hom C B where
  vertex x := ⟨(j.vertex x).symm.toLinearMap,fun n v hv =>
    (j.hom.vertex x).mem_of_map_mem (j.vertex x).injective n _
      (by change j.vertex x ((j.vertex x).symm v) ∈ _
          exact ((j.vertex x).apply_symm_apply v).symm ▸ hv)⟩
  edge e := ⟨(j.edge e).symm.toLinearMap,fun n v hv =>
    (j.hom.edge e).mem_of_map_mem (j.edge e).injective n _
      (by change j.edge e ((j.edge e).symm v) ∈ _
          exact ((j.edge e).apply_symm_apply v).symm ▸ hv)⟩
  lower e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.lower e ((j.vertex (G.source e)).symm v)).trans
        (congrArg (C.forget.lower e) ((j.vertex (G.source e)).apply_symm_apply v))).symm
  upper e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.upper e ((j.vertex (G.target e)).symm v)).trans
        (congrArg (C.forget.upper e) ((j.vertex (G.target e)).apply_symm_apply v))).symm

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b) {C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 include hzero in
 theorem hom_vertex_bijective_of_iso (j : GradedSheaf.Iso B.sheaf C)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map)
    (x : V) : Function.Bijective (f.vertex x).map := by
  let g := j.invHom.comp f
  have hgb : Function.Bijective (g.vertex b).map := (j.vertex b).symm.bijective.comp hb
  have hg := hom_vertex_bijective hzero B B g hgb x
  constructor
  · intro v w h
    apply hg.1
    exact congrArg (j.vertex x).symm h
  · intro w
    obtain ⟨v,hv⟩ := hg.2 ((j.vertex x).symm w)
    exact ⟨v,(j.vertex x).symm.injective hv⟩

 def homIsoOfIso (j : GradedSheaf.Iso B.sheaf C) (hq : C.UpperQuotient α)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map) :
    GradedSheaf.Iso B.sheaf C :=
  f.isoOfBijective (hom_vertex_bijective_of_iso hzero B j f hb)
    (fun e => f.edge_bijective_of_vertex α B.quotient hq e
      (hom_vertex_bijective_of_iso hzero B j f hb _))

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C D : GradedSheaf (𝓐 := 𝓐) G}
  (s : SplitIn B D) (t : SplitIn C D)

 theorem SplitIn.comparison_bijective (x : V)
    (hs : ∀ v, (s.projector.vertex x).map v=v)
    (ht : ∀ v, (t.projector.vertex x).map v=v) :
    Function.Bijective ((t.projection.comp s.inclusion).vertex x).map := by
  let f := ((t.projection.comp s.inclusion).vertex x).map
  let g := ((s.projection.comp t.inclusion).vertex x).map
  have hgf (v : B.vertex x) : g (f v)=v := by
    exact (congrArg (s.projection.vertex x).map (ht ((s.inclusion.vertex x).map v))).trans
      (s.vertex_split x v)
  have hfg (v : C.vertex x) : f (g v)=v := by
    exact (congrArg (t.projection.vertex x).map (hs ((t.inclusion.vertex x).map v))).trans
      (t.vertex_split x v)
  exact ⟨Function.LeftInverse.injective hgf,Function.RightInverse.surjective hfg⟩

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The CANONICAL map from a normalized BMP summand to its adjoint image is
invertible. Consequently the ambient WORD form restricts perfectly on this
particular summand; no such assertion is made for an arbitrary summand. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottCanonicalAdjointHom : GradedSheaf.Hom B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) :=
  (bottSplitAdjointSplit cs basis l hl B s).projection.comp s.inclusion

 theorem bottCanonicalAdjointHom_top_bijective : Function.Bijective
    ((bottCanonicalAdjointHom cs basis l hl B s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map := by
  apply s.comparison_bijective (bottSplitAdjointSplit cs basis l hl B s)
  · exact bottBoundarySplit_top_fixed cs basis l hl _ B s
  · exact bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s

 def bottCanonicalAdjointIso : GradedSheaf.Iso B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let j := (bottBoundarySheaf_iso_adjoint cs basis l hl B s).some
  exact B.homIsoOfIso (symmetricGrading_zero basis) j
    ((bottSplitAdjointSplit cs basis l hl B s).upperQuotient
      (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottCanonicalAdjointHom cs basis l hl B s)
    (bottCanonicalAdjointHom_top_bijective cs basis l hl B s)

 theorem bottCanonicalAdjointIso_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : B.sheaf.vertex x) :
    ((bottCanonicalAdjointIso cs basis l hl B s).vertex x v).val=
      ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
        ((s.inclusion.vertex x).map v) := rfl

end
end KLInvariance.TitsSpace

end


section

/-! On the normalized BMP summand the canonical adjoint recognition proves,
rather than assumes, perfection of the restricted symmetric word form. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottSplitRightWord_fixed (n : B.sheaf.forget.sections Set.univ) :
    bottEndOfSheaf cs basis l hl s.projector (bottSplitRightWord cs basis l hl B.sheaf s n)=
      bottSplitRightWord cs basis l hl B.sheaf s n := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottEndOfSheaf_coordinates,bottSplitRightWord_coordinates]
  change (s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map (n.val x)))=
    (s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

 theorem bottCanonicalAdjointWord (m : B.sheaf.forget.sections Set.univ) :
    bottSplitLeftWord cs basis l hl B.sheaf s
      ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m)=
    bottAdjoint cs l (bottEndOfSheaf cs basis l hl s.projector)
      (bottSplitRightWord cs basis l hl B.sheaf s m) := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottSplitLeftWord_coordinates]
  exact (bottCanonicalAdjointIso_vertex cs basis l hl B s x (m.val x)).trans
    ((congrArg ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
      (bottSplitRightWord_coordinates cs basis l hl B.sheaf s m x).symm).trans
      (bottAdjointSheaf_vertex cs basis l hl s.projector x _))

 def bottCanonicalPerfectPairing : GradedSheaf.PerfectPairing B.sheaf (l.length : ℤ) :=
  bottRecognizedPerfectPairing cs basis l hl B.sheaf s
    (bottCanonicalAdjointIso cs basis l hl B s)

 theorem bottCanonicalPerfectPairing_apply (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      bottSamelsonDuality cs l (bottSplitRightWord cs basis l hl B.sheaf s m)
        (bottSplitRightWord cs basis l hl B.sheaf s n) := by
  change bottSplitAdjointEquivDual cs basis l hl B.sheaf s
    ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m) n=_
  rw [bottSplitAdjointWord_apply,bottCanonicalAdjointWord]
  change bottSamelsonDuality cs l
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (bottEndOfSheaf cs basis l hl s.projector) _) _=_
  rw [PerfectAdjoint.pairing,bottSplitRightWord_fixed]

 theorem bottCanonicalPerfectPairing_symmetric (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      (bottCanonicalPerfectPairing cs basis l hl B s).pairing n m := by
  exact (bottCanonicalPerfectPairing_apply cs basis l hl B s m n).trans
    ((bottSamelson_symmetric cs l _ _).trans
      (bottCanonicalPerfectPairing_apply cs basis l hl B s n m).symm)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure SymmetricPerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ)
    extends PerfectPairing S d where
  symmetric : ∀ m n, pairing m n=pairing n m

 def SymmetricPerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing T d) (j : Iso S T) : SymmetricPerfectPairing S d where
  toPerfectPairing := p.toPerfectPairing.pullback j
  symmetric _m _n := p.symmetric _ _

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 def SymmetricPerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing S d) : SymmetricPerfectPairing (coefficientChange e he S) d where
  toPerfectPairing := p.toPerfectPairing.coefficientChange e he
  symmetric _m _n := congrArg e (p.symmetric _ _)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Unconditional symmetric, integral, support-orthogonal graded perfection
for the actual minimal-boundary sheaves; symmetry is inherited from the
proved canonical-adjoint recognition, not an arbitrary choice of a dual. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricBoundarySheaf_symmetricPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨{ toPerfectPairing := bottCanonicalPerfectPairing cs basis l hl B s
           symmetric := bottCanonicalPerfectPairing_symmetric cs basis l hl B s }⟩

 theorem symmetricBoundarySheaf_symmetricPairing (b : W) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
      (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_symmetricPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace

namespace KLInvariance.BruhatGraph
open Module _root_.OAI.KLInvariance.Graded MomentGraph TitsSpace
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_symmetricPairing :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) := by
  classical
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  let S := symmetricBoundarySheaf cs basis b
  let T := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let e := SymmetricAlgebra.equivMvPolynomial basis
  have he : ∀ n a, a∈symmetricGrading basis n ↔ e a∈polynomialGrading ℝ σ n :=
    mem_symmetricGrading basis
  obtain ⟨p⟩ := symmetricBoundarySheaf_symmetricPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

end
end KLInvariance.BruhatGraph

end


section

/-! The exact degree mechanism needed for the character theorem. Minimality
puts every local intersection coordinate in the positive ideal. A nonzero
homogeneous diagonal then forces the strict half-degree inequality. This
lemma DOES NOT assert the local Hodge/nonzero-diagonal input. -/
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

 include hneg in
 theorem homogeneous_positive_nonzero {n : ℤ} {a : A}
    (ha : a∈𝓐 n) (hp : a∈positiveIdeal 𝓐) (hn : a≠0) : 0<n := by
  by_contra hh
  have hnle : n≤0 := le_of_not_gt hh
  by_cases hz : n=0
  · subst n
    rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg] at hp
    have hc : component 𝓐 0 a=0 := hp
    have he : component 𝓐 0 a=a := DirectSum.decompose_of_mem_same 𝓐 ha
    exact hn (he.symm.trans hc)
  · have hlt : n<0 := lt_of_le_of_ne hnle hz
    rw [hneg n hlt,Submodule.mem_bot] at ha
    exact hn ha

variable {M : Type um} [AddCommGroup M] [Module A M]

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
 theorem dual_mem_ideal (J : Ideal A) (f : Dual A M) {m : M}
    (hm : m∈J • (⊤ : Submodule A M)) : f m∈J := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha v _
    rw [map_smul]
    exact J.mul_mem_right (f v) ha
  · intro u v hu hv
    rw [map_add]
    exact J.add_mem hu hv

variable [Module k M] [IsScalarTower k A M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  {ι : Type ui} [Fintype ι] [DecidableEq ι] (b : Basis ι A M) (d : ι → ℤ)
  (hb : ∀ i, b i∈𝓜 (d i)) (D : ℤ) (Q : Dual A M →ₗ[A] M)

 include hneg hb in
 omit [IsScalarTower k A M] in
 theorem local_diagonal_strict_degree
    (hq : ∀ i, Q (b.dualBasis i)∈𝓜 (D-d i))
    (hmin : LinearMap.range Q ≤ positiveIdeal 𝓐 • (⊤ : Submodule A M))
    (i : ι) (hne : b.dualBasis i (Q (b.dualBasis i))≠0) : 2*d i<D := by
  have hc : b.dualBasis i (Q (b.dualBasis i))∈𝓐 (D-d i+(-d i)) :=
    dualBasis_homogeneous 𝓐 𝓜 b d hb i _ _ (hq i)
  have hp : b.dualBasis i (Q (b.dualBasis i))∈positiveIdeal 𝓐 :=
    dual_mem_ideal (positiveIdeal 𝓐) (b.dualBasis i) (hmin ⟨b.dualBasis i,rfl⟩)
  have hh := homogeneous_positive_nonzero 𝓐 hneg hc hp hne
  omega

end KLInvariance.Graded

end


section

/-! Integral evaluation compatibility of the actual support/dual equivalence. -/
namespace KLInvariance.IntegralSupport
universe ur uv um
variable {R : Type ur} [CommRing R] {V : Type uv} [DecidableEq V]
  {A : V → Type um} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  (M : Submodule R (∀ x, A x)) (p : R)
  (hcut : ∀ x (m : M), (p • Pi.single x (m.val x)) ∈ M)
  [IsDomain R] [∀ x, Module.IsTorsionFree R (A x)] (hp : p≠0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hbalanced : ∀ x m n, d (cut M p hcut x m) n=d m (cut M p hcut x n))
  (x : V) (hπ : Function.Surjective (projection M x))
noncomputable section

 theorem supportEquivDual_pairing (m : supported M x) (n : M) :
    supportEquivDual M p hcut hp d hbalanced x hπ m (projection M x n)=d m.val n := by
  let e := supportEquivDual M p hcut hp d hbalanced x hπ
  have he := congrArg (fun s : supported M x => d s.val n) (e.symm_apply_apply m)
  change d (d.symm ((projection M x).dualMap (e m))) n=d m.val n at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

end
end KLInvariance.IntegralSupport

end


section

/-! Evaluation and symmetry of the actual integral local intersection map.
The support factor is explicitly cancelled only after its nonvanishing is proved. -/

end

end OAI
