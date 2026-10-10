import OAI.RepresentationTheory.KazhdanLusztig.MinimalExtensions

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

structure NonnegativeBasis where
  index : Type um
  finite : Fintype index
  basis : Module.Basis index (MvPolynomial σ k) M
  degree : index → ℕ
  homogeneous : ∀ i, basis i ∈ 𝓜 (degree i)

attribute [instance] NonnegativeBasis.finite

theorem exists_nonnegativeBasis [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) :
    Nonempty (NonnegativeBasis (σ := σ) 𝓜) := by
  classical
  obtain ⟨ι,hι,b,hb⟩ := exists_homogeneous_basis_polynomial (σ := σ) 𝓜 0 hneg
  let := hι
  let : Fintype ι := Fintype.ofFinite ι
  choose d hd using hb
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hh := hd i
    rw [hneg _ (lt_of_not_ge h),Submodule.mem_bot] at hh
    exact b.ne_zero i hh
  exact ⟨⟨ι,inferInstance,b,fun i => (d i).toNat,fun i => by simpa [Int.toNat_of_nonneg (hd0 i)] using hd i⟩⟩

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

noncomputable def polynomial : ℤ[X] := ∑ i, X ^ b.degree i

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma coeff_nonneg (n : ℕ) : 0 ≤ b.polynomial.coeff n := by
  classical
  simp only [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
  exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma eval₂_eq (q : ℝ) : Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial =
    ∑ i, q ^ b.degree i := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) q) (∑ i, X ^ b.degree i) = _
  simp

omit [Finite σ] in
lemma hasSum [Fintype σ] {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial * (1-q)⁻¹ ^ Fintype.card σ) := by
  rw [b.eval₂_eq]
  convert Hilbert.hasSum_homogeneous_basis 𝓜 b.basis (fun i => (b.degree i : ℤ))
    b.homogeneous hq hq1 using 1
  simp

lemma polynomial_eq (c : NonnegativeBasis (σ := σ) 𝓜) : b.polynomial = c.polynomial := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {q | Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))} := by
    intro q hq
    have h := (b.hasSum hq.1 hq.2).unique (c.hasSum hq.1 hq.2)
    have hne : (1-q)⁻¹ ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq.2)))
    change Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))
    simpa only [Polynomial.eval_map] using mul_right_cancel₀ hne h
  exact Set.Infinite.mono hsub (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end NonnegativeBasis

noncomputable def character [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) : ℤ[X] :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial

lemma character_coeff_nonneg [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) (n : ℕ) :
    0 ≤ (character (σ := σ) 𝓜 hneg).coeff n :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.coeff_nonneg n

lemma character_eq [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥)
    (b : NonnegativeBasis (σ := σ) 𝓜) : character (σ := σ) 𝓜 hneg = b.polynomial :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial_eq b

end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk us
variable (k : Type uk) [Field k] (σ : Type us)

 theorem polynomial_scalar_mod_positive (a : MvPolynomial σ k) :
    ∃ c : k, a-algebraMap k (MvPolynomial σ k) c ∈ positiveIdeal (polynomialGrading k σ) := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero k σ _
    (DirectSum.decompose (polynomialGrading k σ) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (polynomialGrading_negative k σ)]
  change component (polynomialGrading k σ) 0 (a-algebraMap k (MvPolynomial σ k) c)=0
  rw [map_sub,hc]
  rw [show component (polynomialGrading k σ) 0
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) =
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (polynomialGrading k σ) a 0).property]
  exact sub_self _

end KLInvariance.Graded

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section


abbrev Coefficient := MvPolynomial σ ℝ

def root (e : Edge cs u b) : PositiveRoot M cs :=
  positiveRootEquiv M cs ⟨label cs u b e,label_isReflection cs u b e⟩

def polynomialLabel (e : Edge cs u b) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val))

 theorem polynomialLabel_homogeneous (e : Edge cs u b) :
    polynomialLabel cs u b basis e ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialLabel
  rw [← basis.sum_repr (embed M (root cs u b e).val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

omit [Fintype σ] in
 theorem polynomialLabel_ne_zero (e : Edge cs u b) :
    polynomialLabel cs u b basis e ≠ 0 := by
  intro he
  have h0 : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) = 0 :=
    (SymmetricAlgebra.equivMvPolynomial basis).injective
      (he.trans (map_zero _).symm)
  have h1 : embed M (root cs u b e).val = 0 :=
    EdgeAlgebra.symmetric_ι_injective (k := ℝ) (h0.trans (map_zero _).symm)
  have h2 := congrArg Prod.fst h1
  exact (root cs u b e).property.1.ne_zero h2


 theorem exists_boundarySheaf (hub : BruhatLE cs u b) :
    Nonempty (BoundarySheaf (polynomialGrading_negative ℝ σ)
      (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact MomentGraph.exists_boundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomial_scalar_mod_positive ℝ σ)
    ⟨b,hub,bruhat_refl cs b⟩ (fun x => x.property.2)
    (polynomialLabel cs u b basis) (polynomialLabel_homogeneous cs u b basis)

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
noncomputable section

def boundarySheaf : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  (exists_boundarySheaf cs u b basis hub).some

def stalkCharacter (x : Interval cs u b) : Polynomial ℤ := by
  let B := boundarySheaf cs u b basis hub
  let := B.free x
  exact Graded.character (σ := σ) (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg

 theorem stalkCharacter_coeff_nonneg (x : Interval cs u b) (n : ℕ) :
    0 ≤ (stalkCharacter cs u b basis hub x).coeff n := by
  let B := boundarySheaf cs u b basis hub
  let := B.free x
  exact Graded.character_coeff_nonneg (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg n


def StalkCharacterObligation : Prop :=
  ∀ x : Interval cs u b, stalkCharacter cs u b basis hub x = klPolynomial cs x.val b


def CostalkFreeObligation : Prop :=
  ∀ x : Interval cs u b, Module.Free (Coefficient (σ := σ))
    (LinearMap.ker ((boundarySheaf cs u b basis hub).sheaf.forget.stalkMap x))

end
end KLInvariance.BruhatGraph

end


section

/-! Parity matching in finite lower Bruhat intervals, used only to construct
actual dihedral interpolation sections. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem simple_mul_bruhat_of_descent {c : W} (i : I)
    (hi : cs.length (cs.simple i*c) < cs.length c) {z : W} (hz : BruhatLE cs z c) :
    BruhatLE cs (cs.simple i*z) c := by
  have h := le_upperSimple cs i (cs.simple i*z)
  rw [upperSimple_mul] at h
  have htop : upperSimple cs i c = c := by simp only [upperSimple,ite_eq_left hi]
  rw [← htop]
  exact bruhat_trans cs h (upperSimple_mono cs i hz)

 theorem lower_parity_balance {c : W} (hc : c ≠ 1) {p : ℕ} (hp : p < 2) :
    ((lowerFinset cs c).filter (fun z => cs.length z % 2 = p)).card =
      ((lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ p)).card := by
  classical
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one hc
  have hmem {z : W} (hz : z ∈ lowerFinset cs c) : cs.simple i*z ∈ lowerFinset cs c :=
    (mem_lowerFinset cs c _).mpr (simple_mul_bruhat_of_descent cs i hi
      ((mem_lowerFinset cs c _).mp hz))
  refine Finset.card_bij (fun z _ => cs.simple i*z) ?_ ?_ ?_
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hmem hz,?_⟩
    have := cs.length_simple_mul z i
    omega
  · intro z hz w hw he
    exact mul_left_cancel he
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine ⟨cs.simple i*z,Finset.mem_filter.mpr ⟨hmem hz,?_⟩,
      cs.simple_mul_simple_cancel_left i⟩
    have := cs.length_simple_mul z i
    omega

 def externalLower (x c : W) : Finset W := by
  classical
  exact (lowerFinset cs c) \ (lowerFinset cs x)

@[simp] theorem mem_externalLower (x c z : W) :
    z ∈ externalLower cs x c ↔ BruhatLE cs z c ∧ ¬ BruhatLE cs z x := by
  classical
  simp [externalLower]

 theorem one_bruhat (x : W) : BruhatLE cs 1 x := by
  obtain ⟨ω,hω,hx⟩ := cs.exists_isReduced x
  simpa only [cs.wordProd_nil,← hx] using bruhat_of_subword cs (List.nil_sublist ω) hω

 theorem external_parity_card_le {x c : W} (hxc : BruhatLE cs x c) :
    ((externalLower cs x c).filter (fun z => cs.length z % 2 = cs.length x % 2)).card ≤
      ((externalLower cs x c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2)).card := by
  classical
  by_cases hc : c = 1
  · subst c
    have hx : x = 1 := bruhat_antisymm cs hxc (one_bruhat cs x)
    subst x
    simp [externalLower]
  have hp : cs.length x % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbal := lower_parity_balance cs hc hp
  have hsub : lowerFinset cs x ⊆ lowerFinset cs c := by
    intro z hz
    exact (mem_lowerFinset cs c z).mpr (((mem_lowerFinset cs x z).mp hz).trans hxc)
  have hs₀ : (lowerFinset cs x).filter (fun z => cs.length z % 2 = cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 = cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have hs₁ : (lowerFinset cs x).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have heq (p : W → Prop) [DecidablePred p] :
      (externalLower cs x c).filter p = (lowerFinset cs c).filter p \ (lowerFinset cs x).filter p := by
    ext z
    simp only [externalLower,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  rw [heq,heq,Finset.card_sdiff_of_subset hs₀,Finset.card_sdiff_of_subset hs₁]
  rw [hbal]
  apply Nat.sub_le_sub_left
  by_cases hx : x = 1
  · subst x
    have hh : lowerFinset cs (1:W) = {1} := by
      ext z
      simp only [mem_lowerFinset,Finset.mem_singleton]
      exact ⟨fun h => bruhat_antisymm cs h (one_bruhat cs z),fun h => h ▸ bruhat_refl cs 1⟩
    simp [hh,Finset.filter_singleton]
  · exact (lower_parity_balance cs hx hp).symm.le

end
end KLInvariance

end


section

/-! Every lower-supported model is an actual Bruhat BMP sheaf on [1,c],
pulled back by the genuine lower-interval graph isomorphism and extended by
zero. Thus its stalk character is not an abstract model selected for convenience. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 abbrev lowerIdealGraph (c : Interval cs 1 b) :=
  lowerGraph (graph cs 1 b) (Set.Iic c) (isLowerSet_Iic c)

 def lowerIntervalMap (c : Interval cs 1 b) :
    GraphMap (lowerIdealGraph cs b c) (graph cs 1 c.val) where
  vertex x := ⟨x.val.val,x.val.property.1,x.property⟩
  edge e := ⟨(⟨(source cs 1 b e.val).val,(source cs 1 b e.val).property.1,
      bruhat_trans cs (.single e.val.property) e.property⟩,
    ⟨(target cs 1 b e.val).val,(target cs 1 b e.val).property.1,e.property⟩),e.val.property⟩
  source _ := rfl
  target _ := rfl

 omit [Fintype I] in
 theorem lowerIntervalMap_injective (c : Interval cs 1 b) :
    Function.Injective (lowerIntervalMap cs b c).vertex := by
  intro x y h
  exact Subtype.ext (Subtype.ext (show x.val.val=y.val.val from
    congrArg (fun z : Interval cs 1 c.val => z.val) h))

 omit [Fintype I] in
 theorem lowerIntervalMap_outgoing (c : Interval cs 1 b)
    (e : Edge cs 1 c.val) (x : Set.Iic c)
    (hx : (lowerIntervalMap cs b c).vertex x=source cs 1 c.val e) :
    ∃ a, (lowerIntervalMap cs b c).edge a=e ∧ (lowerIdealGraph cs b c).source a=x := by
  have hxx := congrArg Subtype.val hx
  let y : Interval cs 1 b := ⟨(target cs 1 c.val e).val,(target cs 1 c.val e).property.1,
    bruhat_trans cs (target cs 1 c.val e).property.2 c.property.2⟩
  let a : Edge cs 1 b := ⟨(x.val,y),hxx.symm ▸ e.property⟩
  refine ⟨⟨a,(target cs 1 c.val e).property.2⟩,?_,?_⟩
  · apply Subtype.ext
    exact Prod.ext hx rfl
  · rfl

 def lowerIntervalBoundary (c : Interval cs 1 b) :
    BoundarySheaf (polynomialGrading_negative ℝ σ) (lowerIdealGraph cs b c)
      (fun e => polynomialLabel cs 1 b basis e.val) ⟨c,Set.mem_Iic.mpr le_rfl⟩ :=
  (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).pullback
    (lowerIntervalMap cs b c) (lowerIntervalMap_injective cs b c)
    (lowerIntervalMap_outgoing cs b c) ⟨c,Set.mem_Iic.mpr le_rfl⟩ rfl

 def boundaryModels : GradedSheaf.BoundaryModels (polynomialGrading_negative ℝ σ)
    (G := graph cs 1 b) (polynomialLabel cs 1 b basis) where
  sheaf c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend
  free c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_free
    (lowerIntervalBoundary cs b basis c).free
  quotient c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_quotient _
    (lowerIntervalBoundary cs b basis c).quotient
  generated c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_generated
    (lowerIntervalBoundary cs b basis c).generated
  flabby c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_flabby
    (lowerIntervalBoundary cs b basis c).flabby.flabby
  support c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_support x hx
  top c := ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex ⟨c,Set.mem_Iic.mpr le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerIntervalBoundary cs b basis c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded (lowerIntervalBoundary cs b basis c).top n _
    ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex_graded ⟨c,Set.mem_Iic.mpr le_rfl⟩ n v hv)
  minimal c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerIntervalBoundary cs b basis c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {M : Type um} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem basis_coordinates_graded {ι : Type ui} [Fintype ι]
    (b : Module.Basis ι A M) (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) :
    ∀ i, b.equivFun m i ∈ 𝓐 (n-d i) := by
  classical
  let : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  have he : ∀ n v, v ∈ shiftedPiece 𝓐 d n → b.equivFun.symm v ∈ 𝓜 n := by
    intro n v hv
    rw [b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)
  have hh := map_component (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm.toLinearMap 0
    (by simpa using he) n (b.equivFun m)
  simp only [sub_zero,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
  rw [show component 𝓜 n m=m from DirectSum.decompose_of_mem_same 𝓜 hm] at hh
  have hc : component (shiftedPiece 𝓐 d) n (b.equivFun m)=b.equivFun m := by
    apply b.equivFun.symm.injective
    exact hh.symm.trans (b.equivFun.symm_apply_apply m).symm
  rw [← hc]
  exact (DirectSum.decompose (shiftedPiece 𝓐 d) (b.equivFun m) n).property

end
end KLInvariance.Graded

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_equiv_shiftedUnits (F : ModuleData.{uk,ua,um} 𝓐) [Module.Free A F] :
    ∃ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ)
      (e : F ≃ₗ[A] pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))),
      ∀ m v, v ∈ F.piece m → e v ∈
        (pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))).piece m := by
  classical
  obtain ⟨ι,hι,b0,hd0⟩ := exists_homogeneous_basis_connected 𝓐 F.piece hneg hzero 0 F.nonneg
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let J := ULift.{um} (Fin n)
  let re : ι ≃ J := (Fintype.equivFin ι).trans Equiv.ulift.symm
  let b := b0.reindex re
  choose dz hdz using hd0
  let d : J → ℕ := fun i => (dz (re.symm i)).toNat
  have hd (i : J) : b i ∈ F.piece (d i : ℤ) := by
    have hz : 0 ≤ dz (re.symm i) := by
      by_contra h
      have he : b0 (re.symm i)=0 := by
        simpa only [F.nonneg _ (lt_of_not_ge h),Submodule.mem_bot] using hdz (re.symm i)
      exact b0.ne_zero (re.symm i) he
    simpa only [b,Module.Basis.reindex_apply,d,Int.toNat_of_nonneg hz] using hdz (re.symm i)
  let e : F ≃ₗ[A] pi (fun i : J => (unit hneg).shift (d i)) :=
    { toFun v i _ := b.equivFun v i
      invFun v := b.equivFun.symm (fun i => v i PUnit.unit)
      left_inv v := b.equivFun.symm_apply_apply v
      right_inv v := by
        funext i j
        change b.equivFun (b.equivFun.symm (fun i => v i PUnit.unit)) i=v i j
        rw [LinearEquiv.apply_symm_apply]
      map_add' v w := by funext i j; exact congrFun (b.equivFun.map_add v w) i
      map_smul' a v := by funext i j; exact congrFun (b.equivFun.map_smul a v) i }
  refine ⟨n,d,e,?_⟩
  intro m v hv i _ j
  change b.equivFun v i ∈ 𝓐 (m-(d i : ℤ)-0)
  rw [sub_zero]
  exact basis_coordinates_graded F.piece b (fun i => (d i : ℤ)) hd m v hv i

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
noncomputable section

 def descend (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) : E →ₗ[R] F :=
  ((LinearMap.ker f).liftQ (g.comp h) hk).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) (v : M) :
    descend f g hf h hk (f v) = g (h v) := by
  simp [descend]

 theorem kernel_scalar_le (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v=r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v=r • w) (h : M →ₗ[R] N) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp h) := by
  intro v hv
  obtain ⟨w,rfl⟩ := (hf v).mp hv
  change g (h (r • w))=0
  rw [h.map_smul]
  exact (hg _).mpr ⟨h w,rfl⟩

end
end KLInvariance.QuotientEdge

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section

 def quotientHom {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map)) : Hom E F where
  map := QuotientEdge.descend f.map g.map hf h.map hk
  graded := by
    intro n v hv
    obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
    rw [QuotientEdge.descend_apply]
    exact g.graded n _ (h.graded n w hw)

 theorem quotientHom_apply {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map))
    (v : M) : (quotientHom f g hf h hk).map (f.map v) = g.map (h.map v) :=
  QuotientEdge.descend_apply _ _ _ _ _ v

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Hom (B C : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (C.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (C.upper e).map ((vertex (G.target e)).map v)

structure OnHom (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) where
  vertex : ∀ x, x ∈ U → ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, G.target e ∈ U → ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.lower e).map v) =
      (C.lower e).map ((vertex (G.source e) hs).map v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.upper e).map v) =
      (C.upper e).map ((vertex (G.target e) ht).map v)

namespace Hom
variable {B C D : GradedSheaf (𝓐 := 𝓐) G}

def comp (g : Hom C D) (f : Hom B C) : Hom B D where
  vertex x := (g.vertex x).comp (f.vertex x)
  edge e := (g.edge e).comp (f.edge e)
  lower e v := by
    change (g.edge e).map ((f.edge e).map ((B.lower e).map v)) = _
    rw [f.lower,g.lower]; rfl
  upper e v := by
    change (g.edge e).map ((f.edge e).map ((B.upper e).map v)) = _
    rw [f.upper,g.upper]; rfl

end Hom

namespace OnHom
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnHom B C U)
noncomputable section

 def ofUniv (j : OnHom B C Set.univ) : Hom B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

 def mapAssignment (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) : C.forget.Assignment := by
  classical
  exact fun y => if h : x < y then (j.vertex y (hx h)).map (f y) else 0

 theorem mapAssignment_at (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (y : V) (h : x < y) :
    j.mapAssignment x hx f y = (j.vertex y (hx h)).map (f y) := by
  classical
  unfold mapAssignment
  exact dite_eq_left h

 theorem compatible (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn (Set.Ioi x) f) :
    C.forget.CompatibleOn (Set.Ioi x) (j.mapAssignment x hx f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at x hx f _ hs,j.mapAssignment_at x hx f _ ht]
  change (C.lower e).map ((j.vertex _ (hx hs)).map (f _)) =
    (C.upper e).map ((j.vertex _ (hx ht)).map (f _))
  exact (j.lower e (hx hs) (hx ht) _).symm.trans
    ((congrArg (j.edge e (hx ht)).map (hf e hs ht)).trans (j.upper e (hx ht) _))

variable [Fintype E]

 def boundary (x : V) (hx : Set.Ioi x ⊆ U) :
    ModuleData.Hom (B.boundary x) (C.boundary x) where
  map := LinearMap.pi fun e =>
    ((j.edge e.val (hx (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))).map).comp
      (LinearMap.proj e)
  graded := by
    intro n v hv e he
    exact (j.edge e.val _).graded n _ (hv e he)

 theorem boundaryMap (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.sections (Set.Ioi x)) :
    (j.boundary x hx).map (B.forget.boundaryMap x f) =
      C.forget.boundaryMap x ⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩ := by
  funext e
  change (j.edge e.val _).map ((B.upper e.val).map (f.val (G.target e.val))) =
    (C.upper e.val).map (j.mapAssignment x hx f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val))]
  exact j.upper e.val _ _

 theorem map_stalk_image_le (x : V) (hx : Set.Ioi x ⊆ U)
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    (LinearMap.range (B.forget.stalkMap x)).map (j.boundary x hx).map ≤
      LinearMap.range (C.forget.stalkMap x) := by
  rw [B.forget.range_stalkMap_eq_boundaryImage hBf hBg,
    C.forget.range_stalkMap_eq_boundaryImage hCf hCg]
  rintro v ⟨w,⟨f,rfl⟩,rfl⟩
  exact ⟨⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩,
    (j.boundaryMap x hx f).symm⟩

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem extend_stalk (x : V) (hx : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)]
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    ∃ f : ModuleData.Hom (B.vertex x) (C.vertex x), ∀ v,
      C.forget.stalkMap x (f.map v) = (j.boundary x hx).map (B.forget.stalkMap x v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        ((j.boundary x hx).map.comp (B.forget.stalkMap x)) (by
          intro v
          exact j.map_stalk_image_le x hx hBf hBg hCf hCg ⟨_,⟨v,rfl⟩,rfl⟩)
      graded := fun n v hv => (j.boundary x hx).graded n _ ((B.stalkHom x).graded n v hv) }
  let π : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hπ : Function.Surjective π.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  obtain ⟨l,hl⟩ := ModuleData.exists_hom_lift hneg hzero π hπ f
  refine ⟨l,fun v => ?_⟩
  exact congrArg (fun z : T => z.val) (LinearMap.congr_fun hl v)

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}

 def castVertexHom {x y : V} (h : x=y)
    (f : ModuleData.Hom (B.vertex x) (C.vertex x)) :
    ModuleData.Hom (B.vertex y) (C.vertex y) := h ▸ f

namespace OnHom
variable {U : Set V} (j : OnHom B C U)
noncomputable section

 def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    OnHom B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → ModuleData.Hom (B.vertex y) (C.vertex y) := fun y hy =>
    if h : y=x then castVertexHom h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castVertexHom]
  let ej : ∀ e, G.target e ∈ insert x U → ModuleData.Hom (B.edge e) (C.edge e) := fun e he =>
    if h : G.target e=x then
      ModuleData.quotientHom (B.upper e) (C.upper e) (hBq e).1 (vj (G.target e) he)
        (QuotientEdge.kernel_scalar_le (B.upper e).map (C.upper e).map (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he).map)
    else j.edge e ((Set.mem_insert_iff.mp he).resolve_left h)
  have ej_old (e : E) (he : G.target e ∈ U) :
      ej e (Set.mem_insert_of_mem x he) = j.edge e he := by
    simp only [ej,dite_eq_right (show G.target e ≠ x from fun h => hx (h ▸ he))]
  refine ⟨vj,ej,?_,?_⟩
  · intro e hs ht v
    have htU : G.target e ∈ U := by
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · exact hmax (lt_of_eq_of_lt hs.symm (G.increasing e))
      · exact hU (G.increasing e).le hs
    rw [ej_old e htU]
    by_cases he : G.source e=x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e=x
    · simp only [ej,dite_eq_left he]
      exact ModuleData.quotientHom_apply _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

 theorem extend_vertex_old (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v))
    (y : V) (hy : y ∈ U) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex y (Set.mem_insert_of_mem x hy) =
      j.vertex y hy := by
  classical
  simp only [extend,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]

 theorem extend_vertex_new (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex x (Set.mem_insert x U) = jv := by
  classical
  dsimp only [extend]
  exact dite_eq_left rfl

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Integral graded lifting of sheaf morphisms. This is the actual minimal
sheaf recognition mechanism needed to split it out of a Bott--Samelson sheaf;
it does not assume or establish the KL character theorem. -/
namespace KLInvariance.MomentGraph.GradedSheaf.OnHom
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A] [Fintype V] [Fintype E] in
private theorem cast_vertex {U U' : Set V} (h : U=U') (j : OnHom B C U)
    (y : V) (hy : y ∈ U') :
    (h ▸ j).vertex y hy = j.vertex y (h.symm ▸ hy) := by
  subst U'
  rfl

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg in
 theorem exists_extension {U : Set V} (hU : IsUpperSet U) (j : OnHom B C U) :
    ∃ f : Hom B C, ∀ x (hx : x ∈ U), f.vertex x = j.vertex x hx := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ j : OnHom B C ((s : Set V)ᶜ),
      ∃ f : Hom B C, ∀ x (hx : x ∈ ((s : Set V)ᶜ)), f.vertex x = j.vertex x hx := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        let jj : OnHom B C Set.univ := heq ▸ j
        refine ⟨jj.ofUniv,fun y hy => ?_⟩
        exact cast_vertex heq j y (Set.mem_univ y)
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        obtain ⟨l,hl⟩ := j.extend_stalk hneg hzero x hmax hBf hBg hCf hCg
        have hout : ∀ e (he : G.source e=x) v,
            (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
              ((B.lower e).map v) =
            (C.lower e).map ((castVertexHom he.symm l).map v) := by
          intro e he v
          subst x
          exact (congrFun (hl v) ⟨e,rfl⟩).symm
        let jj := j.extend hU x hx hmax α hBq hCq l hout
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
        obtain ⟨f,hf⟩ := ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
        refine ⟨f,fun y hy => ?_⟩
        have hy' : y ∈ ((s.erase x : Finset V) : Set V)ᶜ :=
          heq ▸ Set.mem_insert_of_mem x hy
        exact (hf y hy').trans ((cast_vertex heq jj y hy').trans
          (j.extend_vertex_old hU x hx hmax α hBq hCq l hout y hy))
  let s := (Uᶜ).toFinset
  have heq : (s : Set V)ᶜ=U := by simp [s]
  obtain ⟨f,hf⟩ := h s (heq.symm ▸ hU) (heq.symm ▸ j)
  refine ⟨f,fun x hx => ?_⟩
  exact (hf x (heq.symm ▸ hx)).trans (cast_vertex heq.symm j x (heq.symm ▸ hx))

end
end KLInvariance.MomentGraph.GradedSheaf.OnHom

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
  (b : V) (hb : ∀ x, x ≤ b)
noncomputable section

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg hb in
 theorem exists_hom_top (t : ModuleData.Hom (B.vertex b) (C.vertex b)) :
    ∃ f : Hom B C, f.vertex b=t := by
  let je : OnHom B C (∅ : Set V) :=
    { vertex x hx := False.elim hx
      edge e he := False.elim he
      lower e hs := False.elim hs
      upper e ht := False.elim ht }
  have hmax : Set.Ioi b ⊆ (∅ : Set V) := by
    intro x hx
    exact False.elim ((not_lt_of_ge (hb x)) hx)
  have hout : ∀ e (he : G.source e=b) v,
      (je.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm t).map v) := by
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e)))
      (lt_of_eq_of_lt he.symm (G.increasing e)))
  let jj := je.extend isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout
  have hU : IsUpperSet (insert b (∅ : Set V)) := by
    intro x y hxy hx
    have hxb : x=b := by simpa using hx
    subst x
    have hyb : y=b := le_antisymm (hb y) hxy
    simpa using hyb
  obtain ⟨f,hf⟩ := jj.exists_extension hneg hzero α hBq hCq hBfree hBf hBg hCf hCg hU
  exact ⟨f,(hf b (Set.mem_insert b _)).trans
    (je.extend_vertex_new isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout)⟩

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A homogeneous idempotent with image in the positive-ideal multiple of a
bounded-below graded module is zero. This is the minimal-cover rigidity needed
to identify the indecomposable in the BMP construction. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} (M : ModuleData.{uk,ua,um} 𝓐)

 theorem idempotent_eq_zero (f : Hom M M)
    (hi : ∀ v, f.map (f.map v) = f.map v)
    (hm : LinearMap.range f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A M)) :
    f.map = 0 := by
  have hker : LinearMap.ker f.map = ⊤ :=
    eq_top_of_positive_smul_sup 𝓐 M.piece 0 M.nonneg (LinearMap.ker f.map)
      (by
        intro n m h
        change f.map (component M.piece n m) = 0
        rw [← f.component, LinearMap.mem_ker.mp h, map_zero])
      (by
        apply top_unique
        intro m _
        apply Submodule.mem_sup.mpr
        refine ⟨m-f.map m,?_,f.map m,hm ⟨m,rfl⟩,sub_add_cancel _ _⟩
        change f.map (m-f.map m) = 0
        rw [map_sub,hi,sub_self])
  exact LinearMap.ker_eq_top.mp hker

end KLInvariance.Graded.ModuleData

end


section

/-! The actual minimal boundary sheaf is indecomposable: it has no nontrivial
homogeneous idempotent. No KL character or costalk freeness is used here. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Endomorphism (B : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (B.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (B.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (B.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (B.upper e).map ((vertex (G.target e)).map v)

namespace Endomorphism
variable {B : GradedSheaf (𝓐 := 𝓐) G} (f : Endomorphism B)

 def complement : Endomorphism B where
  vertex x :=
    { map := LinearMap.id - (f.vertex x).map
      graded := fun n v hv => (B.vertex x).piece n |>.sub_mem hv ((f.vertex x).graded n v hv) }
  edge e :=
    { map := LinearMap.id - (f.edge e).map
      graded := fun n v hv => (B.edge e).piece n |>.sub_mem hv ((f.edge e).graded n v hv) }
  lower e v := by
    change (B.lower e).map v - (f.edge e).map ((B.lower e).map v) =
      (B.lower e).map (v-(f.vertex (G.source e)).map v)
    rw [map_sub,f.lower]
  upper e v := by
    change (B.upper e).map v - (f.edge e).map ((B.upper e).map v) =
      (B.upper e).map (v-(f.vertex (G.target e)).map v)
    rw [map_sub,f.upper]

 theorem complement_idempotent (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) =
      (f.vertex x).map v) (x : V) (v : B.vertex x) :
    (f.complement.vertex x).map ((f.complement.vertex x).map v) =
      (f.complement.vertex x).map v := by
  change v-(f.vertex x).map v - (f.vertex x).map (v-(f.vertex x).map v) =
    v-(f.vertex x).map v
  rw [map_sub,hi,sub_self,sub_zero]

end Endomorphism
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

 theorem unit_idempotent_trivial [IsDomain A]
    (f : Hom (unit.{uk,ua,um} hneg) (unit.{uk,ua,um} hneg))
    (hi : ∀ v, f.map (f.map v) = f.map v) :
    f.map = 0 ∨ f.map = LinearMap.id := by
  let e : unit.{uk,ua,um} hneg := fun _ => 1
  let c : A := f.map e PUnit.unit
  have expand (v : unit.{uk,ua,um} hneg) : v = v PUnit.unit • e := by
    funext i
    cases i
    exact (mul_one _).symm
  have hf (v : unit.{uk,ua,um} hneg) (i : PUnit.{max ua um + 1}) :
      f.map v i = v PUnit.unit * c := by
    calc
      f.map v i = f.map (v PUnit.unit • e) i := congrArg (fun v => f.map v i) (expand v)
      _ = v PUnit.unit * c := by rw [map_smul]; cases i; rfl
  have hc : c*c=c := by
    have h := congrFun (hi e) PUnit.unit
    rw [hf (f.map e) PUnit.unit] at h
    exact h
  have hz : c*(c-1)=0 := by rw [mul_sub,mul_one,hc,sub_self]
  rcases mul_eq_zero.mp hz with hc | hc
  · left
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_zero]
    rfl
  · right
    have hc : c=1 := sub_eq_zero.mp hc
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_one]
    cases i
    rfl

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)

 theorem idempotent_zero_of_top_zero [Finite V]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v)
    (ht : (f.vertex b).map = 0) :
    (∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0) := by
  have hv : ∀ x, (f.vertex x).map = 0 := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      apply ModuleData.idempotent_eq_zero (B.sheaf.vertex x) (f.vertex x) (hi x)
      intro v hv
      obtain ⟨w,rfl⟩ := hv
      apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
      change B.sheaf.forget.stalkMap x ((f.vertex x).map w) = 0
      funext e
      rcases e with ⟨e,he⟩
      subst x
      change (B.sheaf.lower e).map ((f.vertex (G.source e)).map w) = 0
      rw [← f.lower]
      have hezero : (f.edge e).map = 0 := by
        ext z
        obtain ⟨y,rfl⟩ := (B.quotient e).1 z
        rw [f.upper,ih (G.target e) (G.increasing e)]
        exact map_zero _
      rw [hezero]
      rfl
  refine ⟨hv,?_⟩
  intro e
  ext z
  obtain ⟨y,rfl⟩ := (B.quotient e).1 z
  rw [f.upper,hv]
  exact map_zero _

/-- Actual indecomposability in the idempotent formulation. A direct sum
splitting supplies such a homogeneous idempotent, hence one summand vanishes. -/
 theorem idempotent_trivial [Finite V] [IsDomain A]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v) :
    ((∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0)) ∨
      ((∀ x, (f.vertex x).map = LinearMap.id) ∧
        (∀ e, (f.edge e).map = LinearMap.id)) := by
  have ht : (f.vertex b).map = 0 ∨ (f.vertex b).map = LinearMap.id := by
    have h := B.top
    have general (N : ModuleData.{uk,ua,um} 𝓐) (hN : N=ModuleData.unit hneg)
        (g : ModuleData.Hom N N) (hg : ∀v, g.map (g.map v)=g.map v) :
        g.map=0 ∨ g.map=LinearMap.id := by
      subst N
      exact ModuleData.unit_idempotent_trivial hneg g hg
    exact general _ h (f.vertex b) (hi b)
  rcases ht with ht | ht
  · exact Or.inl (B.idempotent_zero_of_top_zero f hi ht)
  · right
    have hh : (f.complement.vertex b).map = 0 := by
      change LinearMap.id - (f.vertex b).map = 0
      rw [ht,sub_self]
    obtain ⟨hv,he⟩ := B.idempotent_zero_of_top_zero f.complement
      (f.complement_idempotent hi) hh
    constructor
    · intro x
      exact (sub_eq_zero.mp (hv x)).symm
    · intro e
      exact (sub_eq_zero.mp (he e)).symm

end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! A genuine homogeneous self-map of a minimal cover is invertible when its
map on the covered module is invertible. Used for the integral summand bridge. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem MinimalCover.bijective_of_boundaryIso {M : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover M) (f : Hom C.source C.source) (g : M ≃ₗ[A] M)
    (hg : ∀ n v, v ∈ M.piece n → g v ∈ M.piece n)
    (hcomm : ∀ v, C.hom.map (f.map v) = g (C.hom.map v)) :
    Function.Bijective f.map := by
  let gh : Hom M M := ⟨g.toLinearMap,hg⟩
  let gi : Hom M M :=
    { map := g.symm.toLinearMap
      graded := by
        intro n v hv
        apply gh.mem_of_map_mem g.injective n
        change g (g.symm v) ∈ M.piece n
        simpa only [LinearEquiv.apply_symm_apply] using hv }
  let := C.free
  obtain ⟨l,hl⟩ := exists_hom_lift hneg hzero C.hom C.surjective (gi.comp C.hom)
  have hla (v : C.source) : C.hom.map (l.map v) = g.symm (C.hom.map v) :=
    LinearMap.congr_fun hl v
  have hfl : Function.Bijective (f.comp l).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-f.map (l.map v))=0
    rw [map_sub,hcomm,hla,LinearEquiv.apply_symm_apply,sub_self]
  have hlf : Function.Bijective (l.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-l.map (f.map v))=0
    rw [map_sub,hla,hcomm,LinearEquiv.symm_apply_apply,sub_self]
  exact ⟨Function.Injective.of_comp hlf.1,Function.Surjective.of_comp hfl.2⟩

end
end KLInvariance.Graded.ModuleData

end


section

/-! A graded endomorphism of the actual normalized minimal boundary sheaf
is an automorphism as soon as its top component is one. -/
namespace KLInvariance.MomentGraph.GradedSheaf.Endomorphism
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B : GradedSheaf (𝓐 := 𝓐) G}
  (f : Endomorphism B)

 theorem edge_bijective_of_vertex {α : E → A}
    (hBq : B.forget.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  obtain ⟨j,hj⟩ := QuotientEdge.exists_scalar_iso
    (B.upper e).map (B.upper e).map (α e)
    (hBq e).1 (hBq e).1 (hBq e).2 (hBq e).2
    (LinearEquiv.ofBijective (f.vertex (G.target e)).map hv)
  have heq : (f.edge e).map = j.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := (hBq e).1 v
    exact (f.upper e w).trans (hj w).symm
  rw [heq]
  exact j.bijective

end KLInvariance.MomentGraph.GradedSheaf.Endomorphism

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
  (B : BoundarySheaf hneg G α b)
noncomputable section

include hzero in
 theorem endomorphism_bijective_of_top (f : B.sheaf.Endomorphism)
    (ht : Function.Bijective (f.vertex b).map) :
    (∀ x, Function.Bijective (f.vertex x).map) ∧
    (∀ e, Function.Bijective (f.edge e).map) := by
  have hv : ∀ x, Function.Bijective (f.vertex x).map := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      let j : Sheaf.AboveIso B.sheaf.forget B.sheaf.forget x :=
        { vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (ih y hy)
          edge e he := LinearEquiv.ofBijective (f.edge e).map
            (f.edge_bijective_of_vertex B.quotient e (ih _ he))
          lower e he v := f.lower e v
          upper e he v := f.upper e v }
      let T := ModuleData.range (B.sheaf.stalkHom x)
      let g : T ≃ₗ[A] T := LinearEquiv.ofSubmodules j.boundary _ _
        (j.map_stalk_image B.flabby.flabby B.generated B.flabby.flabby B.generated)
      have hg : ∀ n v, v ∈ T.piece n → g v ∈ T.piece n := by
        intro n v hv e he
        exact (f.edge e.val).graded n _ (hv e he)
      let π : ModuleData.Hom (B.sheaf.vertex x) T :=
        { map := (B.sheaf.forget.stalkMap x).rangeRestrict
          graded := fun n v hv => (B.sheaf.stalkHom x).graded n v hv }
      have hπs : Function.Surjective π.map := by
        intro v
        obtain ⟨w,hw⟩ := v.property
        exact ⟨w,Subtype.ext hw⟩
      have hπm : LinearMap.ker π.map ≤
          positiveIdeal 𝓐 • (⊤ : Submodule A (B.sheaf.vertex x)) := by
        intro v hv
        apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
        have hh : π.map v = 0 := LinearMap.mem_ker.mp hv
        exact congrArg (fun z : T => z.val) hh
      let C : ModuleData.MinimalCover T := ⟨B.sheaf.vertex x,B.free x,π,hπs,hπm⟩
      apply C.bijective_of_boundaryIso hneg hzero (f.vertex x) g hg
      intro v
      apply Subtype.ext
      funext e
      change B.sheaf.forget.stalkMap x ((f.vertex x).map v) e =
        (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)
      rcases e with ⟨e,rfl⟩
      exact (f.lower e v).symm
  exact ⟨hv,fun e => f.edge_bijective_of_vertex B.quotient e (hv _)⟩

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

namespace KLInvariance.Graded.ModuleData.Hom
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 def inverse (f : Hom M N) (hf : Function.Bijective f.map) : Hom N M where
  map := (LinearEquiv.ofBijective f.map hf).symm.toLinearMap
  graded := by
    intro n v hv
    apply f.mem_of_map_mem hf.1 n
    change (LinearEquiv.ofBijective f.map hf) ((LinearEquiv.ofBijective f.map hf).symm v) ∈ N.piece n
    simpa only [LinearEquiv.apply_symm_apply] using hv

 theorem map_inverse (f : Hom M N) (hf : Function.Bijective f.map) (v : N) :
    f.map ((f.inverse hf).map v)=v := (LinearEquiv.ofBijective f.map hf).apply_symm_apply v

 theorem inverse_map (f : Hom M N) (hf : Function.Bijective f.map) (v : M) :
    (f.inverse hf).map (f.map v)=v := (LinearEquiv.ofBijective f.map hf).symm_apply_apply v

end
end KLInvariance.Graded.ModuleData.Hom

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 def Hom.toEndomorphism {B : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B B) : Endomorphism B :=
  ⟨f.vertex,f.edge,f.lower,f.upper⟩

 def Hom.inverse {B C : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Hom C B where
  vertex x := (f.vertex x).inverse (hv x)
  edge e := (f.edge e).inverse (he e)
  lower e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.lower,(f.vertex _).map_inverse]
  upper e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.upper,(f.vertex _).map_inverse]

 structure SplitIn (B C : GradedSheaf (𝓐 := 𝓐) G) where
  inclusion : Hom B C
  projection : Hom C B
  vertex_split : ∀ x v, (projection.vertex x).map ((inclusion.vertex x).map v)=v
  edge_split : ∀ e v, (projection.edge e).map ((inclusion.edge e).map v)=v

end
end KLInvariance.MomentGraph.GradedSheaf

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
  (B : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)
  (C : GradedSheaf (𝓐 := 𝓐) G)
  (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

include hzero hb hCq hCfree hCf hCg in
 theorem splitIn_of_top_split
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.SplitIn B.sheaf C) := by
  obtain ⟨ii,hii⟩ := GradedSheaf.exists_hom_top hneg hzero α B.quotient hCq B.free
    B.flabby.flabby B.generated hCf hCg b hb i
  obtain ⟨pp,hpp⟩ := GradedSheaf.exists_hom_top hneg hzero α hCq B.quotient hCfree
    hCf hCg B.flabby.flabby B.generated b hb p
  let f := pp.comp ii
  have ht : Function.Bijective (f.toEndomorphism.vertex b).map := by
    have heq : (f.toEndomorphism.vertex b).map = LinearMap.id := by
      apply LinearMap.ext
      intro v
      change (pp.vertex b).map ((ii.vertex b).map v)=v
      rw [hpp,hii]
      exact hpi v
    rw [heq]
    exact Function.bijective_id
  obtain ⟨hv,he⟩ := B.endomorphism_bijective_of_top hzero f.toEndomorphism ht
  let fi := f.inverse hv he
  refine ⟨⟨ii.comp fi,pp,?_,?_⟩⟩
  · intro x v
    exact (f.vertex x).map_inverse (hv x) v
  · intro e v
    exact (f.edge e).map_inverse (he e) v

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! A minimal graded free cover splits out of every finite graded free cover.
The residual kernel is genuinely graded free over the connected coefficient ring.
This is the local step for decomposing actual flabby word sheaves. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_minimalCover_split {T F : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover T) [Module.Free A F]
    (f : Hom F T) (hf : Function.Surjective f.map) :
    ∃ (g : Hom F C.source) (h : Hom C.source F),
      C.hom.map.comp g.map = f.map ∧ g.map.comp h.map = LinearMap.id := by
  let : Module.Free A C.source := C.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective f
  obtain ⟨t,ht⟩ := exists_hom_lift hneg hzero f hf C.hom
  have hgt : Function.Bijective (g.comp t).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-g.map (t.map v))=0
    rw [map_sub,← LinearMap.comp_apply,hg,← LinearMap.comp_apply,ht,sub_self]
  refine ⟨g,t.comp ((g.comp t).inverse hgt),hg,?_⟩
  ext v
  exact (g.comp t).map_inverse hgt v

 def Hom.splitEquiv {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id) :
    F ≃ₗ[A] C × kernel g := LocalCover.splitEquiv g.map h.map hgh

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] [IsDomain A] in
 theorem Hom.splitEquiv_graded {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id)
    (n : ℤ) (v : F) (hv : v ∈ F.piece n) :
    g.splitEquiv h hgh v ∈ (prod C (kernel g)).piece n := by
  constructor
  · exact g.graded n v hv
  · exact Submodule.sub_mem _ hv (h.graded n _ (g.graded n v hv))

include hneg hzero in
 theorem Hom.kernel_free_of_split {F C : ModuleData.{uk,ua,um} 𝓐}
    [Module.Free A F] (g : Hom F C) (h : Hom C F)
    (hgh : g.map.comp h.map = LinearMap.id) : Module.Free A (kernel g) := by
  let e := g.splitEquiv h hgh
  let p : F →ₗ[A] kernel g := (LinearMap.snd A C (kernel g)).comp e.toLinearMap
  have hp : p.comp g.map.ker.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((v : F) - h.map (g.map v))=v
    rw [LinearMap.mem_ker.mp v.property,map_zero,sub_zero]
  let : Module.Projective A (kernel g) := Module.Projective.of_split g.map.ker.subtype p hp
  obtain ⟨ι,hι,b,_⟩ := exists_homogeneous_basis_connected 𝓐 (kernel g).piece
    hneg hzero 0 (kernel g).nonneg
  exact Module.Free.of_basis b

end
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
 theorem split_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCmin : C.KernelMinimal x) :
    ∃ (g : ModuleData.Hom (B.vertex x) (C.vertex x))
      (e : B.vertex x ≃ₗ[A] C.vertex x × ModuleData.kernel g),
      Module.Free A (ModuleData.kernel g) ∧
      (∀ n v, v ∈ (B.vertex x).piece n →
        e v ∈ (ModuleData.prod (C.vertex x) (ModuleData.kernel g)).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v).1 := by
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
  let p : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hps : Function.Surjective p.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hpm : LinearMap.ker p.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : p.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,p,hps,hpm⟩
  let : Module.Free A (B.vertex x) := hBfree
  obtain ⟨g,h,hg,hgh⟩ := ModuleData.exists_minimalCover_split hneg hzero D f hfs
  refine ⟨g,g.splitEquiv h hgh,g.kernel_free_of_split hneg hzero h hgh,
    g.splitEquiv_graded h hgh,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hg v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

include hzero in
 theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)] :
    ∃ D : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  obtain ⟨g,jv,hfree,hjvgrade,hjv⟩ := (j.toOnIso.above x hmax).split_stalk_graded hneg hzero
    (fun e he => j.edge_graded e (hmax he)) inferInstance (hC.free O x)
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  obtain ⟨n,d,jq0,hjq0⟩ := ModuleData.exists_equiv_shiftedUnits hneg hzero (ModuleData.kernel g)
  let S : GradedSheaf (𝓐 := 𝓐) G := pi (fun i : ULift.{um} (Fin n) => (O.sheaf x).shift (d i))
  let jq1 : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))
      ≃ₗ[A] S.vertex x := LinearEquiv.piCongrRight (fun _ => (O.top x).symm)
  have hjq1 (m : ℤ) (v : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i)))
      (hv : v ∈ (ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))).piece m) :
      jq1 v ∈ (S.vertex x).piece m := by
    intro i _
    let t : ModuleData.Hom ((O.sheaf x).vertex x) (ModuleData.unit hneg) :=
      ⟨(O.top x).toLinearMap,O.top_graded x⟩
    apply t.mem_of_map_mem (O.top x).injective (m-(d i : ℤ))
    change O.top x ((O.top x).symm (v i)) ∈ (ModuleData.unit hneg).piece (m-(d i : ℤ))
    exact ((O.top x).apply_symm_apply (v i)).symm ▸ hv i (Set.mem_univ i)
  let jq := jq0.trans jq1
  let jv' : B.vertex x ≃ₗ[A] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl A (C.vertex x)) jq)
  have hjv' (m : ℤ) (v : B.vertex x) (hv : v ∈ (B.vertex x).piece m) :
      jv' v ∈ ((prod C S).vertex x).piece m :=
    ⟨(hjvgrade m v hv).1,hjq1 m _ (hjq0 m _ (hjvgrade m v hv).2)⟩
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) := by
    let := O.support x y (fun hyx => hx (hU hyx hy))
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).vertex y))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    let := O.support x (G.target e) (fun h => hx (hU h he))
    let : Subsingleton ((O.sheaf x).edge e) := (O.quotient x e).1.subsingleton
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).edge e))
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hsum : ModelSum O.sheaf (insert x U) (prod C S) :=
    .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n d
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = (prod C S).forget.lower e
          (Sheaf.castStalkIso B.forget (prod C S).forget he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact congrFun (hjv v) ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  exact ⟨prod C S,hsum,⟨jj.extend hU x hx hmax α hBq (hsum.quotient O) jv' hjv' hout⟩⟩

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  (B : GradedSheaf (𝓐 := 𝓐) G)

include hzero in
/-- Finite graded decomposition with actual nonnegative shifts. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free A (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated) :
    ∃ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : GradedSheaf (𝓐 := 𝓐) G,
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
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum hzero O hU hC j hBq hBf hBg x hx hmax
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
    ⟨⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩,
      fun x hx => False.elim hx,fun e he => False.elim he⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Graded linear equivalence preserves the genuine free-module character.
This does not assert its identification with any KL polynomial. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

noncomputable def mapNonnegativeBasis (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (b : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece where
  index := b.index
  finite := b.finite
  basis := b.basis.map e
  degree := b.degree
  homogeneous i := he _ _ (b.homogeneous i)

 theorem character_eq_of_gradedEquiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N] (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n) :
    character (σ := σ) M.piece M.nonneg = character (σ := σ) N.piece N.nonneg := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [character_eq M.piece M.nonneg b,
    character_eq N.piece N.nonneg (mapNonnegativeBasis e he b)]
  rfl

end KLInvariance.Graded.ModuleData

end


section

/-! Honest polynomial characters commute with actual finite graded sums and
nonnegative shifts. No Hecke or KL identification enters these lemmas. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 abbrev char [Module.Free (MvPolynomial σ k) M] : Polynomial ℤ :=
  character (σ := σ) M.piece M.nonneg

 def shiftedBasis (b : NonnegativeBasis (σ := σ) M.piece) (d : ℕ) :
    NonnegativeBasis (σ := σ) (M.shift d).piece where
  index := b.index
  finite := b.finite
  basis := b.basis
  degree i := b.degree i+d
  homogeneous i := by
    change b.basis i ∈ M.piece ((b.degree i+d : ℕ)-(d:ℤ))
    simpa only [Nat.cast_add,add_sub_cancel_right] using b.homogeneous i

 instance shift_free [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    Module.Free (MvPolynomial σ k) (M.shift d) := ‹Module.Free (MvPolynomial σ k) M›

 theorem char_shift [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    (M.shift d).char=X^d*M.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.shiftedBasis b d),char,character_eq _ _ b]
  change (∑ i : b.index, (X : Polynomial ℤ) ^ (b.degree i+d)) = X^d*∑ i, X^b.degree i
  simp only [pow_add,mul_comm,Finset.mul_sum]

 def productBasis (b : NonnegativeBasis (σ := σ) M.piece)
    (c : NonnegativeBasis (σ := σ) N.piece) :
    NonnegativeBasis (σ := σ) (M.prod N).piece where
  index := b.index ⊕ c.index
  finite := inferInstance
  basis := b.basis.prod c.basis
  degree := Sum.elim b.degree c.degree
  homogeneous i := by
    cases i with
    | inl i =>
      change ((b.basis.prod c.basis) (Sum.inl i)).1 ∈ M.piece (b.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inl i)).2 ∈ N.piece (b.degree i)
      simpa only [Basis.prod_apply_inl_fst,Basis.prod_apply_inl_snd] using
        And.intro (b.homogeneous i) (Submodule.zero_mem (N.piece (b.degree i)))
    | inr i =>
      change ((b.basis.prod c.basis) (Sum.inr i)).1 ∈ M.piece (c.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inr i)).2 ∈ N.piece (c.degree i)
      simpa only [Basis.prod_apply_inr_fst,Basis.prod_apply_inr_snd] using
        And.intro (Submodule.zero_mem (M.piece (c.degree i))) (c.homogeneous i)

 instance prod_free [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    Module.Free (MvPolynomial σ k) (M.prod N) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (M × N))

 theorem char_prod [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    (M.prod N).char=M.char+N.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  let c := (exists_nonnegativeBasis (σ := σ) N.piece N.nonneg).some
  rw [char,character_eq _ _ (M.productBasis N b c),char,character_eq _ _ b,
    char,character_eq _ _ c]
  change (∑ i : b.index ⊕ c.index, (X : Polynomial ℤ)^Sum.elim b.degree c.degree i) =
    (∑ i : b.index, X^b.degree i)+(∑ i : c.index, X^c.degree i)
  exact Fintype.sum_sum_type (fun i => (X : Polynomial ℤ)^Sum.elim b.degree c.degree i)

 def piBasis {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    (b : ∀ i, NonnegativeBasis (σ := σ) (F i).piece) :
    NonnegativeBasis (σ := σ) (pi F).piece where
  index := Σ i, (b i).index
  finite := inferInstance
  basis := Pi.basis (fun i => (b i).basis)
  degree i := (b i.1).degree i.2
  homogeneous i := by
    classical
    intro j _
    change (Pi.basis (fun i => (b i).basis)) i j ∈ (F j).piece ((b i.1).degree i.2)
    rw [Pi.basis_apply]
    by_cases h : j=i.1
    · subst j
      simpa only [Pi.single_eq_same] using (b i.1).homogeneous i.2
    · simp only [Pi.single_eq_of_ne h,Submodule.zero_mem]

 instance pi_free {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    Module.Free (MvPolynomial σ k) (pi F) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (∀ i, F i))

 theorem char_pi {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    (pi F).char=∑ i, (F i).char := by
  let b := fun i => (exists_nonnegativeBasis (σ := σ) (F i).piece (F i).nonneg).some
  rw [char,character_eq _ _ (piBasis F b)]
  change (∑ i : Σ j, (b j).index, (X : Polynomial ℤ)^(b i.1).degree i.2) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (character_eq (F i).piece (F i).nonneg (b i)).symm

 theorem char_zero [Subsingleton M] [Module.Free (MvPolynomial σ k) M] : M.char=0 := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  have : IsEmpty b.index := ⟨fun i => b.basis.ne_zero i (Subsingleton.elim _ _)⟩
  rw [char,character_eq _ _ b]
  simp [NonnegativeBasis.polynomial]

end
end KLInvariance.Graded.ModuleData

end


section

/-! The character identity of the actual finite shifted-model decomposition.
This is an identity of genuine graded stalk ranks, not a KL assertion. -/

end

end OAI
