import OAI.RepresentationTheory.KazhdanLusztig.EdgeLocalization

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype σ] in
 theorem costalkEquivDual_pairing (d : SectionDuality cs u b basis hub B)
    (x : Interval cs u b) (k : LinearMap.ker (B.sheaf.forget.stalkMap x))
    (n : B.sheaf.forget.sections Set.univ) :
    costalkEquivDual cs u b basis hub B d x k (n.val x)=
      d.pairing (kernelEquivSingleSupport cs u b basis hub B x k).val n := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact IntegralSupport.supportEquivDual_pairing (B.sheaf.forget.sections Set.univ)
    (Sheaf.labelProduct (polynomialLabel cs u b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs u b basis))
    d.pairing d.balanced x (B.sheaf.forget.projection_surjective B.generated x)
    (kernelEquivSingleSupport cs u b basis hub B x k) n

omit [Fintype σ] in
 theorem costalkEquivDual_symmetric (d : SectionDuality cs u b basis hub B)
    (hsym : ∀ m n, d.pairing m n=d.pairing n m)
    (x : Interval cs u b) (k l : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    costalkEquivDual cs u b basis hub B d x k l.val=
      costalkEquivDual cs u b basis hub B d x l k.val := by
  let e := costalkEquivDual cs u b basis hub B d x
  let g := Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x
  let f := kernelEquivSingleSupport cs u b basis hub B x
  have he (k l : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
      g * (e k) l.val=d.pairing (f k).val (f l).val := calc
    g * (e k) l.val = (e k) (g • l.val) := (map_smul (e k) g l.val).symm
    _ = (e k) ((f l).val.val x) := congrArg (e k)
      (kernelEquivSingleSupport_apply cs u b basis hub B x l).symm
    _ = _ := costalkEquivDual_pairing cs u b basis hub B d x k (f l).val
  exact mul_left_cancel₀ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)
    ((he k l).trans ((hsym _ _).trans (he l k).symm))

omit [Fintype σ] in
 theorem costalkEquivDual_inverse_symmetric (d : SectionDuality cs u b basis hub B)
    (hsym : ∀ m n, d.pairing m n=d.pairing n m)
    (x : Interval cs u b) (lam mu : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x)) :
    lam ((costalkEquivDual cs u b basis hub B d x).symm mu).val=
      mu ((costalkEquivDual cs u b basis hub B d x).symm lam).val := by
  have h := costalkEquivDual_symmetric cs u b basis hub B d hsym x
    ((costalkEquivDual cs u b basis hub B d x).symm lam)
    ((costalkEquivDual cs u b basis hub B d x).symm mu)
  simpa only [LinearEquiv.apply_symm_apply] using h

end
end KLInvariance.BruhatGraph

end


section

/-! The genuine BMP local intersection map. All freeness, kernel-minimality and
inverse grading assertions here are now unconditional consequences of the
constructed integral duality. The nonvanishing/Hodge input is deliberately
NOT asserted; the last theorem records precisely how it would force the
strict KL halfdegree bound on ACTUAL homogeneous stalk generators. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 abbrev ActualBoundary := boundarySheaf cs 1 b basis (one_bruhat cs b)

 def actualSymmetricPairing : GradedSheaf.SymmetricPerfectPairing
    (ActualBoundary cs b basis).sheaf (cs.length b : ℤ) :=
  (boundarySheaf_symmetricPairing cs b basis).some

 def actualSectionDuality : SectionDuality cs 1 b basis (one_bruhat cs b)
    (ActualBoundary cs b basis) := by
  let p := actualSymmetricPairing cs b basis
  let B := ActualBoundary cs b basis
  refine ⟨p.pairing,?_⟩
  intro x m n
  exact p.toPerfectPairing.cut_balanced
    (Sheaf.labelProduct (polynomialLabel cs 1 b basis))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs 1 b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs 1 b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m n

 theorem actualSectionDuality_symmetric
    (m n : (ActualBoundary cs b basis).sheaf.sections Set.univ) :
    (actualSectionDuality cs b basis).pairing m n=
      (actualSectionDuality cs b basis).pairing n m :=
  (actualSymmetricPairing cs b basis).symmetric m n

 theorem actualSectionDuality_homogeneous (i j : ℤ)
    (m n : (ActualBoundary cs b basis).sheaf.sections Set.univ)
    (hm : m ∈ ((ActualBoundary cs b basis).sheaf.sections Set.univ).piece i)
    (hn : n ∈ ((ActualBoundary cs b basis).sheaf.sections Set.univ).piece j) :
    (actualSectionDuality cs b basis).pairing m n ∈
      polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)) :=
  (actualSymmetricPairing cs b basis).homogeneous i j m n
    (fun x => hm x (Set.mem_univ x)) (fun x => hn x (Set.mem_univ x))

omit [Fintype (Interval cs 1 b)] in
 theorem costalkFreeObligation : CostalkFreeObligation cs 1 b basis (one_bruhat cs b) :=
  costalk_free_of_duality cs 1 b basis (one_bruhat cs b) _ (actualSectionDuality cs b basis)

 def localIntersection (x : Interval cs 1 b) :
    Dual (Coefficient (σ := σ)) ((ActualBoundary cs b basis).sheaf.vertex x)
      →ₗ[Coefficient (σ := σ)] (ActualBoundary cs b basis).sheaf.vertex x :=
  (LinearMap.ker ((ActualBoundary cs b basis).sheaf.forget.stalkMap x)).subtype.comp
    (costalkEquivDual cs 1 b basis (one_bruhat cs b) _
      (actualSectionDuality cs b basis) x).symm.toLinearMap

omit [Fintype (Interval cs 1 b)] in
 theorem localIntersection_injective (x : Interval cs 1 b) :
    Function.Injective (localIntersection cs b basis x) :=
  Subtype.val_injective.comp (costalkEquivDual cs 1 b basis (one_bruhat cs b) _
    (actualSectionDuality cs b basis) x).symm.injective

omit [Fintype (Interval cs 1 b)] in
 theorem localIntersection_range (x : Interval cs 1 b) :
    LinearMap.range (localIntersection cs b basis x)=
      LinearMap.ker ((ActualBoundary cs b basis).sheaf.forget.stalkMap x) := by
  apply le_antisymm
  · rintro v ⟨lam,rfl⟩
    exact ((costalkEquivDual cs 1 b basis (one_bruhat cs b) _
      (actualSectionDuality cs b basis) x).symm lam).property
  · intro v hv
    refine ⟨costalkEquivDual cs 1 b basis (one_bruhat cs b) _
      (actualSectionDuality cs b basis) x ⟨v,hv⟩,?_⟩
    exact congrArg Subtype.val ((costalkEquivDual cs 1 b basis (one_bruhat cs b) _
      (actualSectionDuality cs b basis) x).symm_apply_apply ⟨v,hv⟩)

omit [Fintype (Interval cs 1 b)] in
 theorem localIntersection_minimal (x : Interval cs 1 b) (hx : x.val≠b) :
    LinearMap.range (localIntersection cs b basis x) ≤ positiveIdeal (polynomialGrading ℝ σ) •
      (⊤ : Submodule (Coefficient (σ := σ)) ((ActualBoundary cs b basis).sheaf.vertex x)) := by
  rw [localIntersection_range]
  apply ((ActualBoundary cs b basis).sheaf.kernelMinimal_iff x).mp
  exact (ActualBoundary cs b basis).minimal x (fun h => hx (congrArg Subtype.val h))

 theorem localIntersection_homogeneous (x : Interval cs 1 b) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) ((ActualBoundary cs b basis).sheaf.vertex x))
    (hlam : ∀ j (v : (ActualBoundary cs b basis).sheaf.vertex x),
      v ∈ ((ActualBoundary cs b basis).sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    localIntersection cs b basis x lam ∈ ((ActualBoundary cs b basis).sheaf.vertex x).piece
      (r+(cs.length b : ℤ)-cs.length x.val) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis (one_bruhat cs b) _
    (actualSectionDuality cs b basis) (cs.length b) (actualSectionDuality_homogeneous cs b basis)
    x r lam hlam
  rw [incoming_card] at h
  exact h

 theorem localIntersection_symmetric (x : Interval cs 1 b)
    (lam mu : Dual (Coefficient (σ := σ)) ((ActualBoundary cs b basis).sheaf.vertex x)) :
    lam (localIntersection cs b basis x mu)=mu (localIntersection cs b basis x lam) :=
  costalkEquivDual_inverse_symmetric cs 1 b basis (one_bruhat cs b) _
    (actualSectionDuality cs b basis) (actualSectionDuality_symmetric cs b basis) x lam mu

 theorem localIntersection_diagonal_strict_degree (x : Interval cs 1 b) (hx : x.val≠b)
    (c : NonnegativeBasis (σ := σ) ((ActualBoundary cs b basis).sheaf.vertex x).piece)
    [DecidableEq c.index] (i : c.index)
    (hdiag : c.basis.dualBasis i (localIntersection cs b basis x (c.basis.dualBasis i))≠0) :
    2*c.degree i<rankDifference cs x.val b := by
  classical
  have hg (j : c.index) := localIntersection_homogeneous cs b basis x (-(c.degree j : ℤ))
    (c.basis.dualBasis j) (dualBasis_homogeneous (polynomialGrading ℝ σ)
      ((ActualBoundary cs b basis).sheaf.vertex x).piece c.basis
      (fun i => (c.degree i : ℤ)) c.homogeneous j)
  have hh := local_diagonal_strict_degree (polynomialGrading ℝ σ)
    (polynomialGrading_negative ℝ σ) ((ActualBoundary cs b basis).sheaf.vertex x).piece
    c.basis (fun i => (c.degree i : ℤ)) c.homogeneous
    ((cs.length b : ℤ)-cs.length x.val) (localIntersection cs b basis x)
    (fun j => by convert hg j using 1; congr 1; omega)
    (localIntersection_minimal cs b basis x hx) i hdiag
  have hlen := length_le_of_bruhat cs x.property.2
  dsimp [rankDifference]
  omega

end
end KLInvariance.BruhatGraph

end


section

/-! Strict later-label membership in a finite nondecreasing schedule,
with arbitrary positions for equal labels. -/
namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem mem_suffix_iff_score_lt (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b))
    (hq : e::q <:+ p) (hf : f ∈ p) (hne : score e ≠ score f) :
    f ∈ q ↔ score e < score f := by
  obtain ⟨a,rfl⟩ := hq
  have h := List.pairwise_append.mp hs
  constructor
  · intro hfq
    exact lt_of_le_of_ne ((List.pairwise_cons.mp h.2.1).1 f hfq) hne
  · intro hlt
    rcases List.mem_append.mp hf with hfa | hfr
    · exact False.elim (not_le_of_gt hlt (h.2.2 f hfa e List.mem_cons_self))
    · rcases List.mem_cons.mp hfr with rfl | hfr
      · exact False.elim (hne rfl)
      · exact hfr

 theorem mem_suffix_iff_score_lt_injective (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b)) (hn : p.Nodup)
    (hq : e::q <:+ p) (hf : f ∈ p) (heq : score e = score f → e=f) :
    f ∈ q ↔ score e < score f := by
  by_cases hne : score e ≠ score f
  · exact mem_suffix_iff_score_lt score hs hq hf hne
  · have hef := heq (not_ne_iff.mp hne)
    subst f
    have hx := (List.nodup_cons.mp (hn.sublist hq.sublist)).1
    simp only [hx,lt_self_iff_false]

end KLInvariance.SchedulePaths

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem shifted_map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  exact Submodule.mem_map.mpr ⟨component 𝓜 (n-d) w,hS (n-d) w hw,
    (map_component 𝓜 𝓝 f d hf n w).symm⟩

 def shiftedImagePieceMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    subPiece 𝓜 S (n-d) →ₗ[k] subPiece 𝓝 (S.map f) n where
  toFun v := ⟨⟨f v.val.val,Submodule.mem_map.mpr ⟨_,v.val.property,rfl⟩⟩,
    by
      change f v.val.val ∈ 𝓝 n
      simpa using hf (n-d) v.val.val v.property⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' c v := by ext; exact (f.restrictScalars k).map_smul c v.val.val

 theorem shiftedImagePieceMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    Function.Surjective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) := by
  rintro ⟨⟨m,hm⟩,hgrad⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  refine ⟨⟨⟨component 𝓜 (n-d) v,hS (n-d) v hv⟩,
    (DirectSum.decompose 𝓜 v (n-d)).property⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (component 𝓜 (n-d) v) = f v
  rw [← map_component 𝓜 𝓝 f d hf n v]
  exact DirectSum.decompose_of_mem_same 𝓝 hgrad

noncomputable def shiftedImagePieceEquiv
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) (n : ℤ) :
    subPiece 𝓜 S (n-d) ≃ₗ[k] subPiece 𝓝 (S.map f) n :=
  LinearEquiv.ofBijective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) ⟨by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    apply hinj
    exact congrArg (fun z => z.val.val) h,
    shiftedImagePieceMap_surjective 𝓜 𝓝 S hS f d hf n⟩

/-- Hilbert series of the actual embedded image of a homogeneous injection. -/
 theorem shifted_image_value
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      q^d * value 𝓜 (S.restrictScalars k) q := by
  have ha := hs.hasSum.mul_left (q^d)
  have hb : HasSum
      (fun n : ℤ => (Module.finrank k (piece 𝓜 (S.restrictScalars k) (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 (S.restrictScalars k) q) := by
    apply (Equiv.addRight d).hasSum_iff.mp
    apply ha.congr_fun
    intro n
    change (Module.finrank k (piece 𝓜 (S.restrictScalars k) (n+d-d)) : ℝ)*q^(n+d) =
      q^d * ((Module.finrank k (piece 𝓜 (S.restrictScalars k) n) : ℝ)*q^n)
    rw [add_sub_cancel_right,zpow_add₀ hq]
    ring
  apply HasSum.tsum_eq
  apply hb.congr_fun
  intro n
  unfold term
  rw [← (subPieceEquiv 𝓝 (S.map f) n).finrank_eq,
    ← (shiftedImagePieceEquiv 𝓜 𝓝 S hS f d hf hinj n).finrank_eq,
    (subPieceEquiv 𝓜 S (n-d)).finrank_eq]

end KLInvariance.Hilbert

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe us um
variable {σ : Type us} [Fintype σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  (B : GradedSheaf (𝓐 := polynomialGrading ℝ σ) G)
noncomputable section

 def kernelHilbert (q : ℝ) (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ℝ :=
  value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars ℝ) q

 def lowerImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.source e) F).map (B.lower e).map

 def upperImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.target e) F).map (B.upper e).map

omit [Fintype σ] in
 theorem upperImage_homogeneous (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    ∀ n v, v ∈ B.upperImage e H → component (B.edge e).piece n v ∈ B.upperImage e H :=
  map_homogeneous (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) H) (B.upwardKernel_homogeneous (G.target e) H)
    (B.upper e).map (B.upper e).graded

 theorem kernelHilbert_edge (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      value (B.edge e).piece ((B.lowerImage e F).restrictScalars ℝ) q := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.source e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.source e)).piece
  have h := B.hilbert_edge_increment (G.source e) F ⟨e,rfl⟩ hq
    (summable_term ℝ σ (B.vertex (G.source e)).piece _ hq hq1)
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

 theorem shifted_upperImage_value (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    value (B.edge e).piece (((B.upperImage e H).map φ).restrictScalars ℝ) q =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.target e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.target e)).piece
  rw [shifted_image_value (B.edge e).piece (B.edge e).piece (B.upperImage e H)
    (B.upperImage_homogeneous e H) φ d hφ hφinj hq.ne'
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)]
  rw [show value (B.edge e).piece ((B.upperImage e H).restrictScalars ℝ) q =
    (1-q) * B.kernelHilbert q (G.target e) H from
      B.upper_image_value α hquot e H ha hreg hinj hq
        (summable_term ℝ σ (B.vertex (G.target e)).piece _ hq hq1)]
  exact (mul_assoc _ _ _).symm


 theorem edge_increment_le (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) ≤
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.edge e).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.edge e).piece
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  exact (summable_term ℝ σ (B.edge e).piece _ hq hq1).tsum_le_tsum
    (term_mono (B.edge e).piece hinc hq)
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)

/-- Even a finite-length or higher-codimension embedded defect is detected by
one positive numerical equality. This does not replace the image inclusion. -/
 theorem edge_increment_eq_iff (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H) ↔
      B.lowerImage e F = (B.upperImage e H).map φ := by
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  constructor
  · intro heq
    have h := polynomial_eq_of_value_eq ℝ σ (B.edge e).piece hinc
      (shifted_map_homogeneous (B.edge e).piece (B.edge e).piece (B.upperImage e H)
        (B.upperImage_homogeneous e H) φ d hφ) hq hq1 heq
    ext v
    exact SetLike.ext_iff.mp h v
  · intro heq
    rw [heq]

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section


 theorem actual_edge_increment_le (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.sheaf.kernelHilbert q ((graph cs u b).source e) F -
      B.sheaf.kernelHilbert q ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) ≤
      q^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-q) *
        B.sheaf.kernelHilbert q ((graph cs u b).target e) H := by
  apply B.sheaf.edge_increment_le (polynomialLabel cs u b basis) B.quotient e F H
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact edgeFactorMap_graded cs basis u b hub B e
  · exact edgeFactorLift_regular cs basis u b hub B e
  · exact hinc
  · exact hq
  · exact hq1

 theorem actual_edge_increment_eq_iff (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (B.sheaf.kernelHilbert q ((graph cs u b).source e) F -
      B.sheaf.kernelHilbert q ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) =
      q^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-q) *
        B.sheaf.kernelHilbert q ((graph cs u b).target e) H) ↔
      B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
        (edgeFactorMap cs basis u b hub B e) := by
  apply B.sheaf.edge_increment_eq_iff (polynomialLabel cs u b basis) B.quotient e F H
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact edgeFactorMap_graded cs basis u b hub B e
  · exact edgeFactorLift_regular cs basis u b hub B e
  · exact hinc
  · exact hq
  · exact hq1

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Comparison

/-- Degree-one labels, `q=t²`, and exactly the source degree
`2*k = length(y)-length(x)-1` give the same coefficient at every edge. -/
 theorem edge_scalar_identity {t : ℝ} (ht : t ≠ 0) (m n k : ℤ)
    (h : m + 2*k = n-1) :
    t^m * (t^2)^k * (1-t^2) = (t⁻¹-t) * t^n := by
  have hp : (t^2)^k = t^(2*k) := by
    rw [zpow_mul]
    norm_num
  rw [hp,← zpow_add₀ ht,h]
  have hsub : t^(n-1) = t^n*t⁻¹ := by
    rw [sub_eq_add_neg,zpow_add₀ ht,zpow_neg_one]
  rw [hsub]
  have hcancel : t⁻¹*t=1 := inv_mul_cancel₀ ht
  calc
    t^n*t⁻¹*(1-t^2) = (t⁻¹-t*(t⁻¹*t))*t^n := by ring
    _ = (t⁻¹-t)*t^n := by rw [hcancel,mul_one]

 theorem transferCoefficient_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < t⁻¹-t := by
  have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
  linarith

 theorem stateScale_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (N : ℕ) (m : ℤ) :
    0 < (1-t^2)^N * t^m := by
  have hsq : t^2 < 1 := by nlinarith
  exact mul_pos (pow_pos (sub_pos.mpr hsq) _) (zpow_pos ht _)

/-- Cancellation of a positive state scale converts an additive normalized
edge identity back to its raw Hilbert-series increment. -/
 theorem scaled_increment_eq_iff (a x y k z : ℝ) (ha : a ≠ 0) :
    a*x = a*y+(a*k)*z ↔ x-y=k*z := by
  constructor
  · intro h
    have he : a*x=a*(y+k*z) := by linear_combination h
    have hc := mul_left_cancel₀ ha he
    linarith
  · intro h
    rw [show x=y+k*z by linarith]
    ring

end KLInvariance.Comparison

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 def stateScale (t : ℝ) (x : Interval cs u b) : ℝ :=
  (1-t^2)^(Fintype.card σ) * t^((cs.length x.val : ℤ)-cs.length b)

omit [Fintype I] in
 theorem stateScale_positive {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : Interval cs u b) : 0 < stateScale (σ := σ) cs u b t x :=
  Comparison.stateScale_pos ht ht1 _ _

 def normalizedKernel (t : ℝ) (x : Interval cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) x)) : ℝ :=
  stateScale (σ := σ) cs u b t x * B.sheaf.kernelHilbert (t^2) x F

 theorem edge_stateScale (e : Edge cs u b) {t : ℝ} (ht : t ≠ 0) :
    stateScale (σ := σ) cs u b t ((graph cs u b).source e) *
      ((t^2)^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-t^2)) =
      (t⁻¹-t) * stateScale (σ := σ) cs u b t ((graph cs u b).target e) := by
  have hd := edgeFactorDegree_edge cs u b e
  have h := Comparison.edge_scalar_identity ht
    ((cs.length (source cs u b e).val : ℤ)-cs.length b)
    ((cs.length (target cs u b e).val : ℤ)-cs.length b)
    (edgeFactorDegree (source cs u b e).val (root cs u b e)) (by omega)
  dsimp only [stateScale,graph]
  calc
    _ = (1-t^2)^(Fintype.card σ) *
        (t^((cs.length (source cs u b e).val : ℤ)-cs.length b) *
          (t^2)^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-t^2)) := by ring
    _ = _ := by rw [h]; ring

/-- A single removal of a later-edge kernel condition has the exact uniform
transfer coefficient `t⁻¹-t` used by the Dyer path matrix. -/
 theorem normalized_edge_increment_le (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    normalizedKernel cs u b basis hub B t ((graph cs u b).source e) F ≤
      normalizedKernel cs u b basis hub B t ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) +
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t ((graph cs u b).target e) H := by
  have h := actual_edge_increment_le cs u b basis hub B e F H hinc
    (sq_pos_of_pos ht) (by nlinarith : t^2 < 1)
  have h' := mul_le_mul_of_nonneg_left h
    (stateScale_positive (σ := σ) cs u b ht ht1 ((graph cs u b).source e)).le
  rw [← mul_assoc,edge_stateScale cs u b e ht.ne',mul_sub] at h'
  simpa only [normalizedKernel,mul_assoc,add_comm] using sub_le_iff_le_add.mp h'

 theorem normalized_edge_increment_eq_iff (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (normalizedKernel cs u b basis hub B t ((graph cs u b).source e) F =
      normalizedKernel cs u b basis hub B t ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) +
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t ((graph cs u b).target e) H) ↔
      B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
        (edgeFactorMap cs basis u b hub B e) := by
  rw [← actual_edge_increment_eq_iff cs u b basis hub B e F H hinc
    (sq_pos_of_pos ht) (by nlinarith : t^2 < 1)]
  have hs := (stateScale_positive (σ := σ) cs u b ht ht1 ((graph cs u b).source e)).ne'
  simp only [normalizedKernel]
  rw [← mul_assoc (t⁻¹-t),← edge_stateScale cs u b e ht.ne']
  exact Comparison.scaled_increment_eq_iff _ _ _ _ _ hs

end
end KLInvariance.BruhatGraph

end


section

/-! Exact numerical endpoints for the actual sheaf, conditional on the two
explicit genuine normalization inputs. These implications are NOT a proof of
existence of the pairing or the Kazhdan--Lusztig character theorem. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 theorem emptyKernel_hilbert (x : Interval cs u b) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.sheaf.kernelHilbert q x ∅ =
      Polynomial.eval₂ (Int.castRingHom ℝ) q (stalkCharacter cs u b basis hub x) *
        (1-q)⁻¹ ^ Fintype.card σ := by
  let _ := B.free x
  let c := (exists_nonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg).some
  have he : B.sheaf.upwardSubmodule x ∅ = ⊤ := by
    ext v
    change (∀ e, e ∈ (∅ : Set (Sheaf.Outgoing (G := graph cs u b) x)) → _) ↔ True
    simp
  rw [GradedSheaf.kernelHilbert,he,Submodule.restrictScalars_top,
    stalkCharacter_eq_character cs u b basis hub B x,
    character_eq (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg c]
  simpa only [Hilbert.value,Hilbert.term_top] using (c.hasSum hq hq1).tsum_eq

 theorem normalized_emptyKernel_of_character (x : Interval cs u b)
    (hc : stalkCharacter cs u b basis hub x = klPolynomial cs x.val b)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    normalizedKernel cs u b basis hub B t x ∅ = scaledKL cs t x.val b := by
  rw [normalizedKernel,emptyKernel_hilbert cs u b basis hub B x
    (sq_pos_of_pos ht) (by nlinarith),hc]
  dsimp only [stateScale,scaledKL]
  have hne : 1-t^2 ≠ 0 := ne_of_gt (by nlinarith : 0 < 1-t^2)
  rw [inv_pow]
  field_simp [hne,inv_pow]

variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
  (C : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)

 theorem normalized_fullKernel_of_duality_character
    (d : SectionDuality cs 1 b basis (one_bruhat cs b) C)
    (hd : ∀ i j (m n : C.sheaf.sections Set.univ),
      m ∈ (C.sheaf.sections Set.univ).piece i → n ∈ (C.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)))
    (x : Interval cs 1 b)
    (hc : stalkCharacter cs 1 b basis (one_bruhat cs b) x = klPolynomial cs x.val b)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) C t x Set.univ =
      scaledKL cs t⁻¹ x.val b := by
  let _ := C.free x
  let c := (exists_nonnegativeBasis (σ := σ) (C.sheaf.vertex x).piece
    (C.sheaf.vertex x).nonneg).some
  have hcp : c.polynomial = klPolynomial cs x.val b := by
    rw [← character_eq (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg c,
      ← stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) C x]
    exact hc
  rw [normalizedKernel,GradedSheaf.kernelHilbert,
    fullKernel_eq cs 1 b basis (one_bruhat cs b) C x,
    costalk_hilbert_of_duality cs 1 b basis (one_bruhat cs b) C d (cs.length b) hd x c
      (sq_pos_of_pos ht) (by nlinarith),hcp,incoming_card cs b x]
  dsimp only [stateScale,scaledKL]
  have hscale : t^((cs.length x.val : ℤ)-cs.length b) *
      (t^2)^((cs.length b : ℤ)-cs.length x.val) =
      (t⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [show (t^2)^((cs.length b : ℤ)-cs.length x.val) =
      t^(2*((cs.length b : ℤ)-cs.length x.val)) by rw [zpow_mul]; norm_num,
      ← zpow_add₀ ht.ne',inv_zpow,← zpow_neg]
    congr 1
    omega
  rw [show (t^2)⁻¹=(t⁻¹)^2 by rw [inv_pow]]
  have hne : 1-t^2 ≠ 0 := ne_of_gt (by nlinarith : 0 < 1-t^2)
  calc
    _ = (t^((cs.length x.val : ℤ)-cs.length b) *
      (t^2)^((cs.length b : ℤ)-cs.length x.val)) *
      Polynomial.eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (klPolynomial cs x.val b) := by
        have hcancel : (1-t^2)^(Fintype.card σ) *
            ((1-t^2)⁻¹)^(Fintype.card σ)=1 := by
          rw [← mul_pow,mul_inv_cancel₀ hne,one_pow]
        calc
          _ = ((1-t^2)^(Fintype.card σ) * ((1-t^2)⁻¹)^(Fintype.card σ)) *
            ((t^((cs.length x.val : ℤ)-cs.length b) *
              (t^2)^((cs.length b : ℤ)-cs.length x.val)) *
              Polynomial.eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (klPolynomial cs x.val b)) := by ring
          _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hscale]

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
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)
noncomputable section

 omit [Fintype σ] in
 theorem restrictBoundary_kernel (x : Interval cs u b) (T : Set (Edge cs 1 b)) :
    (restrictBoundary cs u b basis hub B).sheaf.upwardSubmodule x
      {e | (upperInclusion cs u b).edge e.val ∈ T} =
    B.sheaf.upwardSubmodule ((upperInclusion cs u b).vertex x) {e | e.val ∈ T} := by
  exact B.sheaf.forget.pullback_kernel (upperInclusion cs u b) x T Set.univ
    (fun e he => False.elim (he (Set.mem_univ e)))
    (fun e _ he => upperInclusion_outgoing cs u b e x he)

 theorem normalizedKernel_restrictBoundary (x : Interval cs u b) (T : Set (Edge cs 1 b)) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x
      {e | (upperInclusion cs u b).edge e.val ∈ T} =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) {e | e.val ∈ T} := by
  unfold normalizedKernel GradedSheaf.kernelHilbert
  rw [restrictBoundary_kernel cs u b basis hub B x T]
  rfl

 theorem normalized_emptyKernel_restrictBoundary (x : Interval cs u b) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x ∅ =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) ∅ := by
  simpa only [Set.mem_empty_iff_false,Set.ofPred_false] using
    normalizedKernel_restrictBoundary cs u b basis hub B x ∅ t

 theorem normalized_fullKernel_restrictBoundary (x : Interval cs u b) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x Set.univ =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) Set.univ := by
  simpa only [Set.mem_univ,Set.ofPred_true] using
    normalizedKernel_restrictBoundary cs u b basis hub B x Set.univ t

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.SchedulePaths
universe u v
variable {V : Type u} {E : Type v}
  (source target : E → V)
noncomputable section

 theorem step_monotone (T : ℝ) (hT : 0 ≤ T) (e : E) :
    Monotone (step source target T e) := by
  intro v w hv x
  dsimp [step]
  split_ifs
  · exact add_le_add (hv x) (mul_le_mul_of_nonneg_left (hv _) hT)
  · simpa using hv x

 theorem step_injective (T : ℝ) (e : E) (hne : source e ≠ target e) :
    Function.Injective (step source target T e) := by
  intro v w he
  have ht := congrFun he (target e)
  simp only [step,hne,ite_false,add_zero] at ht
  funext x
  have hx := congrFun he x
  dsimp [step] at hx
  split_ifs at hx with h
  · rw [ht] at hx
    exact add_right_cancel hx
  · exact add_right_cancel hx

 theorem dispatch_monotone (T : ℝ) (hT : 0 ≤ T) (p : List E) :
    Monotone (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact monotone_id
  | cons e p ih => exact (step_monotone source target T hT e).comp ih

 theorem dispatch_injective (T : ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e) :
    Function.Injective (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact Function.injective_id
  | cons e p ih =>
    exact (step_injective source target T e (hne e (by simp))).comp
      (ih (fun a ha => hne a (by simp [ha])))

 theorem dispatch_append' (T : ℝ) (v : V → ℝ) (p q : List E) :
    dispatch source target T v (p++q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

/-- A concrete state indexed by the remaining chronological edge list. -/
 theorem remaining_state_le (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q))) :
    D [] ≤ dispatch source target T (D p) p.reverse := by
  induction p with
  | nil => exact le_rfl
  | cons e p ih =>
    have hp := ih (fun a q hq => hstep a q (hq.trans (List.suffix_cons e p)))
    have he := hstep e p (List.suffix_refl _)
    rw [List.reverse_cons,dispatch_append']
    exact hp.trans (dispatch_monotone source target T hT p.reverse he)

/-- If the endpoint bound is equality, every embedded one-edge Hilbert bound
is equality. Injectivity must be used together with the one-sided bounds. -/
 theorem remaining_steps_eq (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q)))
    (hend : D [] = dispatch source target T (D p) p.reverse) :
    ∀ e q, e::q <:+ p → D q = step source target T e (D (e::q)) := by
  induction p with
  | nil =>
    intro e q hq
    have := hq.length_le
    simp at this
  | cons e p ih =>
    have hps := fun a q (hq : a::q <:+ p) => hstep a q (hq.trans (List.suffix_cons e p))
    have hp := remaining_state_le source target T hT D p hps
    have he := hstep e p (List.suffix_refl _)
    have hm := dispatch_monotone source target T hT p.reverse he
    have hend' : D [] = dispatch source target T
        (step source target T e (D (e::p))) p.reverse := by
      simpa only [List.reverse_cons,dispatch_append',dispatch] using hend
    have hh : dispatch source target T (D p) p.reverse =
        dispatch source target T (step source target T e (D (e::p))) p.reverse := by
      apply le_antisymm hm
      exact hend'.symm.le.trans hp
    have hep : D p = step source target T e (D (e::p)) :=
      dispatch_injective source target T p.reverse
        (fun a ha => hne a (by simp only [List.mem_reverse] at ha; simp [ha])) hh
    have hendpoint : D [] = dispatch source target T (D p) p.reverse := by
      exact hend'.trans hh.symm
    intro a q hq
    rcases List.suffix_cons_iff.mp hq with h | h
    · cases h
      exact hep
    · exact ih (fun a ha => hne a (by simp [ha])) hps hendpoint a q h

end
end KLInvariance.SchedulePaths

end


section

namespace KLInvariance.ReverseFiltration
universe ua um un up
variable {A : Type ua} [CommRing A]
  {M : Type um} [AddCommGroup M] [Module A M]
  {N : Type un} [AddCommGroup N] [Module A N]
  {P : Type up} [AddCommGroup P] [Module A P]

/-- A kernel which is exactly a regular scalar multiple of its domain is
integrally isomorphic to that domain, not just to its fraction-field span. -/
noncomputable def scalarKernelEquiv (g : M →ₗ[A] N) (a : A)
    (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    M ≃ₗ[A] LinearMap.ker g := by
  let f : M →ₗ[A] LinearMap.ker g :=
    (LinearMap.lsmul A M a).codRestrict (LinearMap.ker g) (fun v =>
      (hk (a • v)).mpr ⟨v,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact ha (congrArg Subtype.val h)
  · intro v
    obtain ⟨w,hw⟩ := (hk v.val).mp v.property
    exact ⟨w,Subtype.ext hw.symm⟩


 theorem projective_kernel_of_scalar_presentation
    [Module.Projective A M] [Module.Projective A P]
    (f : P →ₗ[A] N) (g : M →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    Module.Projective A (LinearMap.ker f) := by
  let : Module.Projective A (LinearMap.ker g) :=
    Module.Projective.of_equiv (scalarKernelEquiv g a hk ha)
  exact kernel_projective_of_presentation f g hf hg

 def imageMapKernelEquiv (S : Submodule A M) (f : M →ₗ[A] N) :
    ↥(S ⊓ LinearMap.ker f) ≃ₗ[A] LinearMap.ker (Hilbert.imageMap S f) where
  toFun v := ⟨⟨v.val,v.property.1⟩,Subtype.ext v.property.2⟩
  invFun v := ⟨v.val.val,v.val.property,congrArg Subtype.val v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scaled equality of two *embedded* images constructs a presentation with
regular scalar kernel. This is the pure module-algebra form of the reverse
freeness step, allowing arbitrary image codimension. -/
 theorem inf_kernel_projective_of_image_eq
    (S : Submodule A M) (T : Submodule A P)
    [Module.Projective A S] [Module.Projective A T]
    (f : M →ₗ[A] N) (g : P →ₗ[A] N) (φ : N →ₗ[A] N)
    (hφ : Function.Injective φ) (himage : S.map f = (T.map g).map φ)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ T → v ∈ T)
    (ha : Function.Injective (fun v : P => a • v)) :
    Module.Projective A ↥(S ⊓ LinearMap.ker f) := by
  let j : T →ₗ[A] S.map f := ((φ.comp g).comp T.subtype).codRestrict (S.map f) (by
    intro v
    rw [himage]
    exact Submodule.mem_map.mpr ⟨g v.val,Submodule.mem_map.mpr ⟨v.val,v.property,rfl⟩,rfl⟩)
  have hj : Function.Surjective j := by
    intro v
    have hv : v.val ∈ (T.map g).map φ := himage ▸ v.property
    obtain ⟨w,hw,hwv⟩ := Submodule.mem_map.mp hv
    obtain ⟨z,hz,hzw⟩ := Submodule.mem_map.mp hw
    exact ⟨⟨z,hz⟩,Subtype.ext ((congrArg φ hzw).trans hwv)⟩
  have hjker (v : T) : j v = 0 ↔ ∃ w : T, v = a • w := by
    constructor
    · intro hv
      have hv' : φ (g v.val) = 0 := congrArg Subtype.val hv
      have hz : g v.val = 0 := hφ (hv'.trans (map_zero φ).symm)
      obtain ⟨w,hw⟩ := (hk v.val).mp hz
      refine ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      apply Subtype.ext
      change φ (g (a • w.val)) = 0
      rw [(hk (a • w.val)).mpr ⟨w.val,rfl⟩,map_zero]
  have haT : Function.Injective (fun v : T => a • v) := by
    intro v w hvw
    exact Subtype.ext (ha (congrArg Subtype.val hvw))
  let : Module.Projective A (LinearMap.ker (Hilbert.imageMap S f)) :=
    projective_kernel_of_scalar_presentation (Hilbert.imageMap S f) j
      (Hilbert.imageMap_surjective S f) hj a hjker haT
  exact Module.Projective.of_equiv (imageMapKernelEquiv S f).symm

end KLInvariance.ReverseFiltration

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
/-- The reverse-freeness step uses precisely the already free upper kernel
and the preceding lower kernel, plus the actual embedded image equality. -/
 theorem partial_kernel_projective_of_image_eq (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)]
    [Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)]
    (heq : B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e)) :
    Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)) := by
  rw [B.sheaf.upwardKernel_insert]
  apply ReverseFiltration.inf_kernel_projective_of_image_eq
    (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)
    (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)
    (B.sheaf.lower e).map (B.sheaf.upper e).map (edgeFactorMap cs basis u b hub B e)
    (edgeFactorLift_regular cs basis u b hub B e) heq
    (polynomialLabel cs u b basis e) (B.quotient e).2
  · apply B.sheaf.upwardSubmodule_saturated
    intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _

 theorem partial_kernel_free_of_image_eq (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)]
    [Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)]
    (heq : B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e)) :
    Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)) := by
  let D := B.sheaf.upwardKernel ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)
  let : Module.Projective (Coefficient (σ := σ)) D :=
    partial_kernel_projective_of_image_eq cs u b basis hub B e F H heq
  obtain ⟨ι,_,bs,_⟩ := exists_homogeneous_basis_polynomial (k := ℝ) (σ := σ)
    D.piece 0 D.nonneg
  exact Module.Free.of_basis bs

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 def remainingConditions (p : List (Edge cs u b)) (x : Interval cs u b) :
    Set (Sheaf.Outgoing (G := graph cs u b) x) := {f | f.val ∈ p}

omit [Fintype I] in
 theorem remainingConditions_nil (x : Interval cs u b) :
    remainingConditions cs u b [] x = ∅ := by ext f; simp [remainingConditions]

omit [Fintype I] in
 theorem remainingConditions_cons_source (e : Edge cs u b) (p : List (Edge cs u b)) :
    remainingConditions cs u b (e::p) (source cs u b e) =
      insert ⟨e,rfl⟩ (remainingConditions cs u b p (source cs u b e)) := by
  ext f
  simp only [remainingConditions,Set.mem_ofPred_eq,List.mem_cons,Set.mem_insert_iff]
  rw [Subtype.ext_iff]

omit [Fintype I] in
 theorem remainingConditions_cons_other (e : Edge cs u b) (p : List (Edge cs u b))
    (x : Interval cs u b) (hne : source cs u b e ≠ x) :
    remainingConditions cs u b (e::p) x = remainingConditions cs u b p x := by
  ext f
  have hf : f.val ≠ e := by
    intro he
    exact hne (he ▸ f.property)
  simp [remainingConditions,hf]

 def scheduleState (t : ℝ) (p : List (Edge cs u b)) : Interval cs u b → ℝ :=
  fun x => normalizedKernel cs u b basis hub B t x (remainingConditions cs u b p x)

 theorem scheduleState_step (e : Edge cs u b) (p : List (Edge cs u b))
    (hinc : B.sheaf.lowerImage e (remainingConditions cs u b p ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b p ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    scheduleState cs u b basis hub B t p ≤
      step (source cs u b) (target cs u b) (t⁻¹-t) e
        (scheduleState cs u b basis hub B t (e::p)) := by
  classical
  intro x
  by_cases hx : (graph cs u b).source e = x
  · subst x
    have h := normalized_edge_increment_le cs u b basis hub B e
      (remainingConditions cs u b p ((graph cs u b).source e))
      (remainingConditions cs u b p ((graph cs u b).target e)) hinc ht ht1
    have hne : source cs u b e ≠ target cs u b e :=
      ne_of_lt ((graph cs u b).increasing e)
    change normalizedKernel cs u b basis hub B t (source cs u b e)
        (remainingConditions cs u b p (source cs u b e)) ≤
      normalizedKernel cs u b basis hub B t (source cs u b e)
        (remainingConditions cs u b (e::p) (source cs u b e)) +
      if source cs u b e = source cs u b e then
        (t⁻¹-t) * normalizedKernel cs u b basis hub B t (target cs u b e)
          (remainingConditions cs u b (e::p) (target cs u b e)) else 0
    rw [ite_eq_left rfl,remainingConditions_cons_source,
      remainingConditions_cons_other cs u b e p (target cs u b e) hne]
    exact h
  · simp only [scheduleState,step]
    have hx' : source cs u b e ≠ x := hx
    rw [ite_eq_right hx',add_zero,remainingConditions_cons_other cs u b e p x hx]

 theorem scheduleState_le (p : List (Edge cs u b))
    (hinc : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    scheduleState cs u b basis hub B t [] ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub B t p) p.reverse := by
  exact remaining_state_le _ _ _ (Comparison.transferCoefficient_pos ht ht1).le _ p
    (fun e q hq => scheduleState_step cs u b basis hub B e q (hinc e q hq) ht ht1)


 theorem edgeImages_eq_of_scheduleState_eq (p : List (Edge cs u b))
    (hinc : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hend : scheduleState cs u b basis hub B t [] =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub B t p) p.reverse) :
    ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) =
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e) := by
  classical
  have heq := remaining_steps_eq (source cs u b) (target cs u b) (t⁻¹-t)
    (Comparison.transferCoefficient_pos ht ht1).le
    (scheduleState cs u b basis hub B t) p
    (fun e _ => ne_of_lt ((graph cs u b).increasing e))
    (fun e q hq => scheduleState_step cs u b basis hub B e q (hinc e q hq) ht ht1) hend
  intro e q hq
  apply (normalized_edge_increment_eq_iff cs u b basis hub B e
    (remainingConditions cs u b q ((graph cs u b).source e))
    (remainingConditions cs u b q ((graph cs u b).target e)) (hinc e q hq) ht ht1).mp
  have h := congrFun (heq e q hq) ((graph cs u b).source e)
  have hne : source cs u b e ≠ target cs u b e :=
    ne_of_lt ((graph cs u b).increasing e)
  change normalizedKernel cs u b basis hub B t (source cs u b e)
      (remainingConditions cs u b q (source cs u b e)) =
    normalizedKernel cs u b basis hub B t (source cs u b e)
      (remainingConditions cs u b (e::q) (source cs u b e)) +
    (if source cs u b e = source cs u b e then
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t (target cs u b e)
        (remainingConditions cs u b (e::q) (target cs u b e)) else 0) at h
  rw [ite_eq_left rfl,remainingConditions_cons_source,
    remainingConditions_cons_other cs u b e q (target cs u b e) hne] at h
  exact h

end
end KLInvariance.BruhatGraph

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 def transportedSlope (e : Edge cs u b) : ℝ :=
  geometricSlope (AdaptedDyer.rootLabel cs' (transportedEdge φ e))

 def chronologicalSchedule : List (Edge cs u b) := (transportedSchedule φ).reverse

omit [Fintype I] in
 theorem transportedScore_eq (e : Edge cs u b) : transportedScore φ e =
    toLex (transportedSlope φ e,transportedSlope φ e) := by
  unfold transportedScore lexEdgeScore lexRootScore transportedSlope
  rw [geometricFunctional_normalizedRoot]

omit [Fintype I] in
 theorem chronologicalSchedule_pairwise : (chronologicalSchedule φ).Pairwise
    (fun e f => transportedSlope φ e ≤ transportedSlope φ f) := by
  rw [chronologicalSchedule,List.pairwise_reverse]
  apply (transportedSchedule_pairwise φ).imp
  intro e f h
  have hh := Prod.Lex.monotone_fst _ _ h
  rw [transportedScore_eq,transportedScore_eq] at hh
  exact hh

omit [Fintype I] in
 theorem chronologicalSchedule_nodup : (chronologicalSchedule φ).Nodup :=
  List.nodup_reverse.mpr (transportedSchedule_nodup φ)

omit [Fintype I] in
 theorem chronologicalSchedule_full (e : Edge cs u b) : e ∈ chronologicalSchedule φ :=
  List.mem_reverse.mpr (transportedSchedule_full φ e)

omit [Fintype I] in
 theorem transportedSlope_source_unique (e f : Edge cs u b)
    (hs : source cs u b e=source cs u b f)
    (h : transportedSlope φ e=transportedSlope φ f) : e=f := by
  have hr := congrArg rootRef (geometricSlope_injective h)
  rw [AdaptedDyer.rootRef_rootLabel,AdaptedDyer.rootRef_rootLabel] at hr
  change (φ (target cs u b e)).val * (φ (source cs u b e)).val⁻¹ =
    (φ (target cs u b f)).val * (φ (source cs u b f)).val⁻¹ at hr
  rw [hs] at hr
  apply Subtype.ext
  exact Prod.ext hs (φ.injective (Subtype.ext (mul_right_cancel hr)))

omit [Fintype I] in
 theorem transportedSlope_path_ne (e f : Edge cs u b)
    (hs : target cs u b e=source cs u b f) :
    transportedSlope φ e ≠ transportedSlope φ f := by
  intro h
  exact AdaptedDyer.rootLabel_ne_of_join cs' (transportedEdge φ e) (transportedEdge φ f)
    (congrArg (fun x => (φ x).val) hs) (geometricSlope_injective h)

omit [Fintype I] in
 theorem suffix_source_iff {e f : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) (hf : source cs u b f=source cs u b e) :
    f ∈ q ↔ transportedSlope φ e < transportedSlope φ f :=
  mem_suffix_iff_score_lt_injective (transportedSlope φ) (chronologicalSchedule_pairwise φ)
    (chronologicalSchedule_nodup φ) hq (chronologicalSchedule_full φ f)
    (transportedSlope_source_unique φ e f hf.symm)

omit [Fintype I] in
 theorem suffix_target_iff {e f : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) (hf : source cs u b f=target cs u b e) :
    f ∈ q ↔ transportedSlope φ e < transportedSlope φ f :=
  mem_suffix_iff_score_lt (transportedSlope φ) (chronologicalSchedule_pairwise φ)
    hq (chronologicalSchedule_full φ f) (transportedSlope_path_ne φ e f hf.symm)

omit [Fintype I] in
 theorem ambientLater_upperInclusion (e f : Edge cs u b) :
    (upperInclusion cs u b).edge f ∈ ambientLater φ
      (AdaptedDyer.rootLabel cs' (transportedEdge φ e)) ↔
    transportedSlope φ e < transportedSlope φ f := by
  have hs : BruhatStep cs' (φ (source cs u b f)).val (φ (target cs u b f)).val :=
    (transportedEdge φ f).property
  have hiff : ambientAfterIndicator (φ (source cs u b f)).val
      (AdaptedDyer.rootLabel cs' (transportedEdge φ e))
      (φ (target cs u b f)).val = 1 ↔ transportedSlope φ e < transportedSlope φ f := by
    simp only [ambientAfterIndicator,dite_eq_left hs]
    change (if transportedSlope φ e < transportedSlope φ f then 1 else 0)=1 ↔ _
    split_ifs <;> simp_all
  constructor
  · rintro ⟨_,h⟩
    exact hiff.mp h
  · intro h
    exact ⟨(source cs u b f).property.1,hiff.mpr h⟩

omit [Fintype I] in
 theorem remainingConditions_source_ambient {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) :
    remainingConditions cs u b q (source cs u b e) =
      {f | (upperInclusion cs u b).edge f.val ∈ ambientLater φ
        (AdaptedDyer.rootLabel cs' (transportedEdge φ e))} := by
  ext f
  exact (suffix_source_iff φ hq f.property).trans (ambientLater_upperInclusion φ e f.val).symm

omit [Fintype I] in
 theorem remainingConditions_target_ambient {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) :
    remainingConditions cs u b q (target cs u b e) =
      {f | (upperInclusion cs u b).edge f.val ∈ ambientLater φ
        (AdaptedDyer.rootLabel cs' (transportedEdge φ e))} := by
  ext f
  exact (suffix_target_iff φ hq f.property).trans (ambientLater_upperInclusion φ e f.val).symm

end
end KLInvariance.BruhatGraph

end


section


end

end OAI
