import OAI.RepresentationTheory.KazhdanLusztig.Support

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

def SectionDualityObligation : Prop :=
  ∃ d : SectionDuality cs 1 b basis (one_bruhat cs b)
    (boundarySheaf cs 1 b basis (one_bruhat cs b)),
    ∀ i j (m n : (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ),
      m ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece i →
      n ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ))

end
end KLInvariance.BruhatGraph

end


section

/-! Balance of a two-sided perfect pairing needs orthogonality on both
sides, not equality of its two integral embeddings into an ambient form. -/
namespace BalancedCuts
universe ur um ua
variable {R : Type ur} [CommRing R] [IsDomain R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {A : Type ua} [AddCommGroup A] [Module R A]
  (d : M →ₗ[R] Module.Dual R M) (π : M →ₗ[R] A) (c : M →ₗ[R] M)
  (p : R) (hp : p≠0) (hπ : ∀ m, π (c m)=p • π m)
  (hleft : ∀ m n, π n=0 → d (c m) n=0)
  (hright : ∀ m n, π m=0 → d m (c n)=0)

include hp hπ hleft hright in
 theorem balanced_two (m n : M) : d (c m) n=d m (c n) := by
  have hn : π (p • n-c n)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have hm : π (p • m-c m)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have en := hleft m _ hn
  have em := hright _ n hm
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,sub_eq_zero] at en em
  exact mul_left_cancel₀ hp (en.trans em.symm)

end BalancedCuts

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [IsDomain A] [DecidableEq V]
  {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ} (p : PerfectPairing S d)
  (a : A) (ha : a≠0)
  (hcut : ∀ x (m : S.forget.sections Set.univ), a • Pi.single x (m.val x)∈S.forget.sections Set.univ)
noncomputable section

 include ha in
 theorem PerfectPairing.cut_balanced (x : V) (m n : S.forget.sections Set.univ) :
    p.pairing (IntegralSupport.cut _ a hcut x m) n =
      p.pairing m (IntegralSupport.cut _ a hcut x n) := by
  apply BalancedCuts.balanced_two p.pairing.toLinearMap
    (IntegralSupport.projection (S.forget.sections Set.univ) x)
    (IntegralSupport.cut _ a hcut x) a ha
    (IntegralSupport.cut_self _ a hcut x)
  · intro v w hw
    exact p.left_orthogonal x _ w (fun y hy => IntegralSupport.cut_other _ a hcut x y hy v) hw
  · intro v w hv
    exact p.right_orthogonal x v _ hv (fun y hy => IntegralSupport.cut_other _ a hcut x y hy w)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem sectionDualityObligation_of_perfectPairing
    (p : GradedSheaf.PerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) :
    SectionDualityObligation cs b basis := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  refine ⟨⟨p.pairing,?_⟩,?_⟩
  · intro x m n
    exact p.cut_balanced (Sheaf.labelProduct (polynomialLabel cs 1 b basis))
      (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs 1 b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs 1 b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m n
  · intro i j m n hm hn
    exact p.homogeneous i j m n (fun x => hm x (Set.mem_univ x))
      (fun x => hn x (Set.mem_univ x))

end
end KLInvariance.BruhatGraph

end


section

/-! Integral costalk duality only uses free stalks, the genuine edge quotients,
generation and a perfect support-orthogonal section form. No top/minimality or
KL character assumption is needed. This extension applies to genuine words. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))

structure FreeSheaf where
  sheaf : GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b)
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient (polynomialLabel cs u b basis)
  generated : sheaf.forget.Generated

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section
 def kernelEquivSingleSupport (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      IntegralSupport.supported (B.sheaf.forget.sections Set.univ) x := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (x : Interval cs u b) : Module.Finite (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) :=
    (B.sheaf.vertex x).finite
  let _ (x : Interval cs u b) : Fintype (Module.Free.ChooseBasisIndex
      (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)) := Fintype.ofFinite _
  let bs := fun x : Interval cs u b =>
    Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)
  exact (B.sheaf.forget.kernelEquivSingleStalk (polynomialLabel cs u b basis)
    (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).2) bs x
    (incoming_pairwise_relPrime cs u b basis x)
    (B.sheaf.forget.outgoing_product_regular (polynomialLabel cs u b basis)
      (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).1)
      (fun e => (B.quotient e).2) bs x
      (outgoing_incoming_not_dvd cs u b basis x))).trans
        (B.sheaf.forget.singleStalkEquivSupport x)


structure SectionDuality where
  pairing : B.sheaf.forget.sections Set.univ ≃ₗ[Coefficient (σ := σ)]
    Dual (Coefficient (σ := σ)) (B.sheaf.forget.sections Set.univ)
  balanced : ∀ x m n,
    pairing (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m) n =
    pairing m (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x n)

 def costalkEquivDual (d : SectionDuality cs u b basis B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

 theorem costalk_free_of_duality (d : SectionDuality cs u b basis B)
    (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ)) (LinearMap.ker (B.sheaf.forget.stalkMap x)) := by
  let _ := B.free x
  exact Module.Free.of_equiv (costalkEquivDual cs u b basis B d x).symm

 variable [Fintype σ] [Fintype (Interval cs u b)]

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis B x)
        ((kernelEquivSingleSupport cs u b basis B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

 def fullSubmodule (x : Interval cs u b) : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x) :=
    LinearMap.ker (B.sheaf.forget.stalkMap x)

omit [Fintype σ] [Fintype (Edge cs u b)] [Fintype (Interval cs u b)]
  [DecidableEq (Interval cs u b)] in
 theorem fullKernel_eq (x : Interval cs u b) :
    B.sheaf.upwardSubmodule x Set.univ = fullSubmodule cs u b basis B x := by
  ext m
  change (∀ e ∈ Set.univ, B.sheaf.forget.stalkMap x m e = 0) ↔ B.sheaf.forget.stalkMap x m = 0
  simp only [Set.mem_univ,forall_const]
  exact funext_iff.symm

 def fullKernel (x : Interval cs u b) : ModuleData (polynomialGrading ℝ σ) :=
  ModuleData.sub (B.sheaf.vertex x) (fullSubmodule cs u b basis B x) (by
    simpa only [fullKernel_eq cs u b basis B x] using
      B.sheaf.upwardKernel_homogeneous x Set.univ)

 theorem costalk_hilbert_of_duality
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (c : NonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Hilbert.value (B.sheaf.vertex x).piece
      ((fullSubmodule cs u b basis B x).restrictScalars ℝ) q =
      q^(l-(Sheaf.incoming (G := graph cs u b) x).card) *
        Polynomial.eval₂ (Int.castRingHom ℝ) q⁻¹ c.polynomial *
        (1-q)⁻¹ ^ Fintype.card σ := by
  classical
  let K := fullKernel cs u b basis B x
  let cb : Basis c.index (Coefficient (σ := σ)) K :=
    c.basis.dualBasis.map (costalkEquivDual cs u b basis B d x).symm
  have hcb (i : c.index) : cb i ∈ K.piece
      (l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) := by
    change ((costalkEquivDual cs u b basis B d x).symm (c.basis.dualBasis i)).val ∈
      (B.sheaf.vertex x).piece _
    have h := costalkEquivDual_inverse_homogeneous cs u b basis B d l hd x
      (-(c.degree i : ℤ)) (c.basis.dualBasis i)
      (dualBasis_homogeneous (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
        c.basis (fun i => (c.degree i : ℤ)) c.homogeneous i)
    simpa only [show -(c.degree i : ℤ)+l-(Sheaf.incoming (G := graph cs u b) x).card =
      l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ) by omega] using h
  have hs := Hilbert.hasSum_homogeneous_basis K.piece cb
    (fun i => l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) hcb hq hq1
  have hv : Hilbert.value K.piece ⊤ q =
      (∑ i, q^(l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ))) *
        (1-q)⁻¹ ^ Fintype.card σ := by
    simpa only [Hilbert.value,Hilbert.term_top] using hs.tsum_eq
  change Hilbert.value (B.sheaf.vertex x).piece
    ((fullSubmodule cs u b basis B x).restrictScalars ℝ) q = _
  rw [← Hilbert.value_subPiece]
  change Hilbert.value K.piece ⊤ q = _
  rw [hv,c.eval₂_eq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hq.ne',zpow_natCast,div_eq_mul_inv,inv_pow]


 def dualityOfPairing {l : ℤ} (p : GradedSheaf.PerfectPairing B.sheaf l) :
    SectionDuality cs u b basis B where
  pairing := p.pairing
  balanced := p.cut_balanced
    (Sheaf.labelProduct (polynomialLabel cs u b basis))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs u b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)))

end
end FreeSheaf
end KLInvariance.BruhatGraph

end


section

/-! The finite sums used by the actual local decomposition. The model criteria
are kept explicit here; they are not asserted for the constructed BMP object
or inserted into the main KL theorem. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}


instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (R := R) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit)

instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (R := R) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit)

structure LocalModels (α : E → R) where
  sheaf : V → Sheaf.{u,v,w,z} (R := R) G
  free : ∀ c x, Module.Free R ((sheaf c).vertex x)
  finite : ∀ c x, Module.Finite R ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).Generated
  flabby : ∀ c, (sheaf c).Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[R] R
  minimal : ∀ c x, x ≠ c → LinearMap.ker ((sheaf c).stalkMap x) ≤
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((sheaf c).vertex x))

inductive ModelSum (O : V → Sheaf.{u,v,w,z} (R := R) G) (U : Set V) :
    Sheaf.{u,v,w,z} (R := R) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ n : ℕ,
      ModelSum O U (prod B (pi (fun _ : Fin n => O c)))

namespace ModelSum
variable {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {U : Set V} {B : Sheaf.{u,v,w,z} (R := R) G}

omit [IsLocalRing R] in
lemma mono {O : V → Sheaf.{u,v,w,z} (R := R) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n ih => exact .add ih c (hUT hc) n

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Free R (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma finite (h : ModelSum O.sheaf U B) (x : V) : Module.Finite R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Finite R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Finite R (C.vertex x) := ih
    let _ := O.finite c x
    change Module.Finite R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | add _ c _ n ih => exact prod_upperQuotient _ _ α ih (pi_upperQuotient _ α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.Generated := by
  induction h with
  | zero => exact fun x v => ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n ih => exact prod_generated _ _ ih (pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n ih => exact prod_flabby _ _ ih (pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) :
    LinearMap.ker (B.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (B.vertex x)) := by
  induction h with
  | zero =>
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | add _ c hc n ih =>
    exact prod_minimal _ _ x _ ih (pi_minimal _ x _
      (fun _ => O.minimal c x (fun he => hx (he ▸ hc))))

end ModelSum
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue uz
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

/-- Equality of embedded images with a scalar on the upper image. -/
def ScaledImages (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) : Prop :=
  ∀ z : B.edge e,
    (∃ v ∈ B.upwardKernel (G.source e) F, B.lower e v=z) ↔
    ∃ w ∈ B.upwardKernel (G.target e) H, r • B.upper e w=z

theorem scaledImages_iff (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    B.ScaledImages e F H r ↔
      (B.upwardKernel (G.source e) F).map (B.lower e) =
        r • (B.upwardKernel (G.target e) H).map (B.upper e) := by
  constructor
  · intro h
    ext z
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change (∃ v, v ∈ B.upwardKernel (G.source e) F ∧ B.lower e v=z) ↔ _
    rw [h z]
    constructor
    · rintro ⟨w,hw,he⟩
      exact ⟨B.upper e w,⟨w,hw,rfl⟩,he⟩
    · rintro ⟨t,⟨w,hw,rfl⟩,he⟩
      exact ⟨w,hw,he⟩
  · intro h z
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv' : B.lower e v ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        h ▸ (show B.lower e v ∈ (B.upwardKernel (G.source e) F).map (B.lower e) from ⟨v,hv,rfl⟩)
      obtain ⟨t,⟨w,hw,rfl⟩,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv'
      exact ⟨w,hw,he⟩
    · rintro ⟨w,hw,rfl⟩
      have hw' : r • B.upper e w ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨B.upper e w,⟨w,hw,rfl⟩,rfl⟩
      rw [← h] at hw'
      exact hw'

theorem prod_upwardKernel_iff (B C : Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (prod B C).vertex x) :
    v ∈ (prod B C).upwardKernel x F ↔
      v.1 ∈ B.upwardKernel x F ∧ v.2 ∈ C.upwardKernel x F := by
  constructor
  · intro h
    constructor
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.fst (h ⟨e,rfl⟩ he)
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.snd (h ⟨e,rfl⟩ he)
  · rintro ⟨hB,hC⟩ ⟨e,heq⟩ he
    subst x
    exact Prod.ext (hB ⟨e,rfl⟩ he) (hC ⟨e,rfl⟩ he)

theorem pi_upwardKernel_iff {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (pi B).vertex x) :
    v ∈ (pi B).upwardKernel x F ↔ ∀ i, v i ∈ (B i).upwardKernel x F := by
  constructor
  · rintro h i ⟨e,heq⟩ he
    subst x
    exact congrFun (h ⟨e,rfl⟩ he) i
  · rintro h ⟨e,heq⟩ he
    subst x
    exact funext (fun i => h i ⟨e,rfl⟩ he)

theorem prod_scaledImages (B C : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : B.ScaledImages e F H r) (hC : C.ScaledImages e F H r) :
    (prod B C).ScaledImages e F H r := by
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ F v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mp ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mp ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ H _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ H v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mpr ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mpr ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ F _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩

theorem pi_scaledImages {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : ∀ i, (B i).ScaledImages e F H r) : (pi B).ScaledImages e F H r := by
  classical
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ F v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mp ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ H _).mpr hw,funext hwe⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ H v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mpr ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ F _).mpr hw,funext hwe⟩

theorem zero_scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    (zero : Sheaf.{ur,uv,ue,uz} (R := R) G).ScaledImages e F H r := by
  intro z
  constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

theorem ModelSum.scaledImages {O : V → Sheaf.{ur,uv,ue,uz} (R := R) G}
    {U : Set V} {B : Sheaf.{ur,uv,ue,uz} (R := R) G} (h : ModelSum O U B)
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hO : ∀ c ∈ U, (O c).ScaledImages e F H r) : B.ScaledImages e F H r := by
  induction h with
  | zero => exact zero_scaledImages e F H r
  | add _ c hc n ih =>
    exact prod_scaledImages _ _ e F H r ih
      (pi_scaledImages (fun _ : Fin n => O c) e F H r (fun _ => hO c hc))

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Actual full upward kernels commute with finite graded sums, shifts and
sheaf isomorphisms. No freeness is inferred without a free model. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 abbrev kernelData (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :=
  B.upwardKernel x Set.univ

 def kernelProdEquiv (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (prod B C) x ≃ₗ[A] ((kernelData B x).prod (kernelData C x)) where
  toFun m := ⟨⟨m.val.1,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).1⟩,
    ⟨m.val.2,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).2⟩⟩
  invFun m := ⟨⟨m.1.val,m.2.val⟩,(Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ _).mpr
    ⟨m.1.property,m.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem kernelProdEquiv_graded (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (prod B C) x) (hv : v∈(kernelData (prod B C) x).piece n) :
    kernelProdEquiv B C x v∈((kernelData B x).prod (kernelData C x)).piece n := hv

 def kernelPiEquiv {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (pi B) x ≃ₗ[A] ModuleData.pi (fun i => kernelData (B i) x) where
  toFun m i := ⟨m.val i,(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ m.val).mp m.property i⟩
  invFun m := ⟨(fun i => (m i).val),(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ _).mpr
    (fun i => (m i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem kernelPiEquiv_graded {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (pi B) x) (hv : v∈(kernelData (pi B) x).piece n) :
    kernelPiEquiv B x v∈(ModuleData.pi (fun i => kernelData (B i) x)).piece n := hv

 def kernelShiftEquiv (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ) :
    kernelData (B.shift d) x ≃ₗ[A] (kernelData B x).shift d := LinearEquiv.refl A _

 theorem kernelShiftEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ)
    (n : ℤ) (v : kernelData (B.shift d) x) (hv : v∈(kernelData (B.shift d) x).piece n) :
    kernelShiftEquiv B x d v∈((kernelData B x).shift d).piece n := hv

 def Iso.kernelEquiv {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V) :
    kernelData B x ≃ₗ[A] kernelData C x where
  toFun m := ⟨j.vertex x m.val,(j.toIso.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  invFun m := ⟨(j.vertex x).symm m.val,(j.toIso.symm.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  left_inv m := Subtype.ext ((j.vertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((j.vertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (j.vertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (j.vertex x) a m.val)

 theorem Iso.kernelEquiv_graded {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V)
    (n : ℤ) (v : kernelData B x) (hv : v∈(kernelData B x).piece n) :
    j.kernelEquiv x v∈(kernelData C x).piece n := j.vertex_graded x n v.val hv

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 instance kernelShiftFree (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    Module.Free (MvPolynomial σ k) (kernelData (B.shift d) x) :=
  Module.Free.of_equiv (kernelShiftEquiv B x d).symm

 instance kernelProdFree (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    Module.Free (MvPolynomial σ k) (kernelData (prod B C) x) :=
  Module.Free.of_equiv (kernelProdEquiv B C x).symm

 instance kernelPiFree {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    Module.Free (MvPolynomial σ k) (kernelData (pi B) x) :=
  Module.Free.of_equiv (kernelPiEquiv B x).symm

 instance kernelZeroFree (x : V) :
    Module.Free (MvPolynomial σ k) (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  infer_instance

 theorem kernelChar_shift (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    (kernelData (B.shift d) x).char=X^d*(kernelData B x).char := by
  rw [← ModuleData.char_shift _ d]
  exact ModuleData.character_eq_of_gradedEquiv (kernelShiftEquiv B x d)
    (kernelShiftEquiv_graded B x d)

 theorem kernelChar_prod (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    (kernelData (prod B C) x).char=(kernelData B x).char+(kernelData C x).char := by
  rw [← ModuleData.char_prod]
  exact ModuleData.character_eq_of_gradedEquiv (kernelProdEquiv B C x)
    (kernelProdEquiv_graded B C x)

 theorem kernelChar_pi {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    (kernelData (pi B) x).char=∑ i, (kernelData (B i) x).char := by
  rw [← ModuleData.char_pi]
  exact ModuleData.character_eq_of_gradedEquiv (kernelPiEquiv B x) (kernelPiEquiv_graded B x)

 theorem kernelChar_zero (x : V) :
    (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x).char=0 := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact ModuleData.char_zero _

 theorem ModelSum.kernelFree {O : V → GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (hf : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O U B) (x : V) : Module.Free (MvPolynomial σ k) (kernelData B x) := by
  induction h with
  | zero => infer_instance
  | @add C _ c _ n d ih =>
    let _ := ih
    let _ := hf c x
    infer_instance

 def freeKernelChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (kernelData B x).char

 theorem ModelSum.character_both [Fintype V] {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O.sheaf U B) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B (h.free O) x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B (h.kernelFree hk) x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  classical
  induction h with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · intro x
      change ((GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)).vertex x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact ModuleData.char_zero _
    · intro x
      change (kernelData (GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)) x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact kernelChar_zero (σ := σ) (G := G) x
  | @add B h c hc n d ih =>
    obtain ⟨m,hm,heq,hkeq⟩ := ih
    let a : Polynomial ℤ := ∑ i, X^(d i)
    have ha (r : ℕ) : 0 ≤ a.coeff r := by
      simp only [a,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
      exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    refine ⟨fun y => m y+if y=c then a else 0,?_,?_,?_⟩
    · intro y r
      rw [Polynomial.coeff_add]
      apply add_nonneg (hm y r)
      split
      · exact ha r
      · simp
    · intro x
      let _ := h.free O x
      let _ := O.free c x
      change ((B.vertex x).prod (ModuleData.pi (fun i => ((O.sheaf c).vertex x).shift (d i)))).char = _
      rw [ModuleData.char_prod,ModuleData.char_pi]
      simp only [ModuleData.char_shift]
      change freeStalkChar B (h.free O) x + _ = _
      rw [heq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    · intro x
      let _ := h.kernelFree hk x
      let _ := hk c x
      change (kernelData (prod B (pi (fun i => (O.sheaf c).shift (d i)))) x).char = _
      rw [kernelChar_prod,kernelChar_pi]
      simp only [kernelChar_shift]
      change freeKernelChar B (h.kernelFree hk) x + _ = _
      rw [hkeq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section
 def kernelEquivFull (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData B x ≃ₗ[A] LinearMap.ker (B.forget.stalkMap x) where
  toFun m := ⟨m.val,funext (fun e => m.property e (Set.mem_univ e))⟩
  invFun m := ⟨m.val,fun e _ => congrFun m.property e⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 def kernelDual (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData B.sheaf x :=
  (costalkEquivDual cs 1 b basis B d x).symm.trans (B.sheaf.kernelEquivFull x).symm

omit [Fintype (Interval cs 1 b)] in
 theorem kernel_free (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ)) (GradedSheaf.kernelData B.sheaf x) := by
  let := B.free x
  exact Module.Free.of_equiv (kernelDual cs b basis B d x)

 theorem kernelDual_homogeneous (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (x : Interval cs 1 b) (hn : cs.length x.val≤n) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v∈(B.sheaf.vertex x).piece j →
      lam v∈polynomialGrading ℝ σ (j+r)) :
    kernelDual cs b basis B d x lam∈(GradedSheaf.kernelData B.sheaf x).piece
      (r+(n-cs.length x.val : ℕ)) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis B d n hd x r lam hlam
  rw [incoming_card] at h
  change ((costalkEquivDual cs 1 b basis B d x).symm lam).val∈
    (B.sheaf.vertex x).piece (r+↑(n-cs.length x.val))
  have he : r+(n:ℤ)-cs.length x.val=r+↑(n-cs.length x.val) := by omega
  rwa [he] at h

 theorem kernel_character (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (hn : cs.length b≤n) (x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar B.sheaf (kernel_free cs b basis B d) x=
      Polynomial.reflect (n-cs.length x.val) (GradedSheaf.freeStalkChar B.sheaf B.free x) := by
  let := B.free x
  let := kernel_free cs b basis B d x
  exact ModuleData.char_of_dual_equiv _ _ (kernelDual cs b basis B d x) _
    (kernelDual_homogeneous cs b basis B d n hd x ((length_le_of_bruhat cs x.property.2).trans hn))

end
end KLInvariance.BruhatGraph.FreeSheaf

end


section

/-! Genuine word costalk character from the integral word pairing, transported
along the fixed symmetric-algebra coordinate isomorphism. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottSection_left_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : ∀ y, y≠x → m.val y=0) (hn : n.val x=0) :
    bottSectionDuality cs l hl m n=0 := by
  obtain ⟨a,rfl⟩ := bottSection_surjective cs l hl m
  obtain ⟨b,rfl⟩ := bottSection_surjective cs l hl n
  rw [bottSectionDuality_apply]
  exact bottStalk_supported_annihilates cs l hl x a b hm hn

 theorem bottSection_right_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : m.val x=0) (hn : ∀ y, y≠x → n.val y=0) :
    bottSectionDuality cs l hl m n=0 := by
  rw [bottSection_symmetric]
  exact bottSection_left_orthogonal cs l hl x n m hn hm

 def bottWordPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (l.length : ℤ) where
  pairing := bottSectionDuality cs l hl
  homogeneous := bottSectionDuality_homogeneous cs basis l hl
  left_orthogonal := bottSection_left_orthogonal cs l hl
  right_orthogonal := bottSection_right_orthogonal cs l hl

 def bottPolynomialPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) (l.length : ℤ) :=
  (bottWordPerfectPairing cs basis l hl).coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis)

 def bottFreeSheaf (l : List I) : FreeSheaf cs 1 (cs.wordProd l) basis where
  sheaf := bottPolynomialSheaf cs basis l 1 (cs.wordProd l)
  free := bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)
  quotient := bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l)
  generated := bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l)

local instance finiteEdges (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
local instance (a : Type*) : DecidableEq a := Classical.decEq a

 def bottFreeDuality (l : List I) (hl : cs.IsReduced l) :
    FreeSheaf.SectionDuality cs 1 (cs.wordProd l) basis (bottFreeSheaf cs basis l) :=
  FreeSheaf.dualityOfPairing cs 1 (cs.wordProd l) basis _ (bottPolynomialPerfectPairing cs basis l hl)

 theorem bottKernelFree (l : List I) (hl : cs.IsReduced l) (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) x) :=
  FreeSheaf.kernel_free cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl) x

 theorem bottKernelCharacter (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=Polynomial.reflect (rankDifference cs x.val (cs.wordProd l))
        (bottStalkCharacter cs basis l x.val) := by
  have he : cs.length (cs.wordProd l)=l.length := hl
  change _=Polynomial.reflect (cs.length (cs.wordProd l)-cs.length x.val) _
  rw [he]
  apply FreeSheaf.kernel_character cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl)
    l.length _ he.le x
  intro i j m a hm ha
  exact (bottPolynomialPerfectPairing cs basis l hl).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

end
end KLInvariance.TitsSpace

end


section

/-! Bar and the exact R-convolution for genuine positive Hecke words.
No KL character or degree estimate is assumed. -/
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem one_add_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : I) (v : Space W C) :
    v+leftInv cs q i v=(↑q⁻¹:C) • (v+left cs (q:C) i v) := by
  rw [leftInv_apply,smul_sub,smul_smul,smul_add]
  have h : (↑q⁻¹:C)*((q:C)-1)=1-(↑q⁻¹:C) := by rw [mul_sub,q.inv_mul,mul_one]
  rw [h,sub_smul,one_smul]
  module

 theorem barLinear_positiveWord (cs : CoxeterSystem M W) (q : Cˣ) (l : List I) :
    barLinear cs q (positiveWord cs (↑q⁻¹:C) l)=
      (↑q⁻¹:C)^l.length • positiveWord cs (q:C) l := by
  induction l with
  | nil => simp [barBasis_one]
  | cons i l ih =>
    simp only [positiveWord,map_add]
    have h := congrArg (fun f : Module.End C (Space W C) => f (positiveWord cs (↑q⁻¹:C) l))
      (barLinear_left cs q i)
    simp only [Module.End.mul_apply] at h
    rw [h,ih,map_smul,← smul_add,one_add_leftInv,smul_smul,List.length_cons,pow_succ]

 theorem positiveWord_support (cs : CoxeterSystem M W) (q : C) (l : List I)
    (hl : cs.IsReduced l) : (positiveWord cs q l).support ⊆ lowerFinset cs (cs.wordProd l) := by
  classical
  induction l with
  | nil => simpa [positiveWord,Hecke.basis,lowerFinset] using
      (show (Finsupp.single 1 (1:C)).support ⊆ lowerFinset cs 1 by
        intro x hx
        by_cases h : x=1
        · subst x; exact (mem_lowerFinset cs 1 1).mpr .refl
        · simp [Finsupp.mem_support_iff,Ne.symm h] at hx)
  | cons i l ih =>
    have ht : cs.IsReduced l := by simpa using hl.drop 1
    have ha : ¬cs.length (cs.simple i*cs.wordProd l)<cs.length (cs.wordProd l) := by
      have h := hl.eq
      simp only [cs.wordProd_cons,List.length_cons,←ht.eq] at h
      omega
    intro x hx
    apply (mem_lowerFinset cs (cs.wordProd (i::l)) x).mpr
    have step (y : W) (hy : BruhatLE cs y (cs.wordProd l)) :
        BruhatLE cs (upperSimple cs i y) (cs.wordProd (i::l)) := by
      simpa only [upperSimple,ite_eq_right ha,cs.wordProd_cons] using upperSimple_mono cs i hy
    have h : positiveWord cs q l x≠0 ∨ positiveWord cs q l (cs.simple i*x)≠0 := by
      by_contra hn
      push Not at hn
      rw [Finsupp.mem_support_iff,positiveWord_cons_coeff,hn.1,hn.2] at hx
      split_ifs at hx <;> simp_all
    rcases h with h|h
    · exact (le_upperSimple cs i x).trans
        (step x ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h))))
    · have hh := step (cs.simple i*x)
        ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h)))
      rw [upperSimple_mul] at hh
      exact (le_upperSimple cs i x).trans hh

 theorem positiveWord_rValue (cs : CoxeterSystem M W) (q : Cˣ) (l : List I)
    (hl : cs.IsReduced l) (x : W) :
    ∑ z ∈ lowerFinset cs (cs.wordProd l), rValue cs q x z * positiveWord cs (q:C) l z=
      (↑q⁻¹:C)^cs.length x * (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_positiveWord cs q⁻¹ l)
  simp only [inv_inv] at h
  rw [barLinear,Finsupp.linearCombination_apply,Finsupp.sum_apply,
    Finsupp.sum_of_support_subset _ (positiveWord_support cs (q:C) l hl) _ (by simp)] at h
  simp only [Finsupp.smul_apply,smul_eq_mul] at h
  have hr (z : W) : rValue cs q x z=(↑q⁻¹:C)^cs.length x * barBasis cs q⁻¹ z x := by
    simpa using rValue_inverse_eq_barBasis cs q⁻¹ x z
  simp only [hr,mul_assoc,←Finset.mul_sum]
  rw [show (∑ z ∈ lowerFinset cs (cs.wordProd l), barBasis cs q⁻¹ z x * positiveWord cs (q:C) l z)=
      (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x by
    simpa only [mul_comm] using h]

end
end KLInvariance.HeckeQ

end


section

namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem eval_positiveWord (cs : CoxeterSystem M W) (q : C) (l : List I) (x : W) :
    Polynomial.eval₂ (Int.castRingHom C) q
      (positiveWord cs (Polynomial.X : Polynomial ℤ) l x)=positiveWord cs q l x := by
  classical
  induction l generalizing x with
  | nil => simp only [positiveWord_nil,Hecke.basis,Finsupp.single_apply]; split_ifs <;> simp
  | cons i l ih =>
    rw [positiveWord_cons_coeff,positiveWord_cons_coeff]
    split_ifs <;> simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,
      Polynomial.eval₂_X,ih]

end
end KLInvariance.HeckeQ

end


section

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_natDegree_le_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    M.char.natDegree≤l := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using M.degree_le_of_dual_equiv N e l he c i

end
end KLInvariance.Graded.ModuleData

end


section

/-! Genuine word stalk-to-costalk R-convolution, derived from the Hecke bar
and the constructed integral perfect word pairing. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (a : Type*) : DecidableEq a := Classical.decEq a
local instance rWordEdges (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
local instance rWordInterval (l : List I) : Fintype (Interval cs 1 (cs.wordProd l)) := by
  let := interval_finite cs 1 (cs.wordProd l)
  exact Fintype.ofFinite _

 theorem bottStalkCharacter_natDegree_le (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    (bottStalkCharacter cs basis l x.val).natDegree≤rankDifference cs x.val (cs.wordProd l) := by
  let B := bottFreeSheaf cs basis l
  let := B.free x
  change (B.sheaf.vertex x).char.natDegree≤rankDifference cs x.val (cs.wordProd l)
  apply ModuleData.char_natDegree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl) x)
    (rankDifference cs x.val (cs.wordProd l))
  have hd := (bottPolynomialPerfectPairing cs basis l hl).homogeneous
  have he : cs.length (cs.wordProd l)=l.length := hl
  apply FreeSheaf.kernelDual_homogeneous cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl)
    (cs.length (cs.wordProd l)) _ x (length_le_of_bruhat cs x.property.2)
  intro i j m a hm ha
  rw [he]
  exact hd i j m a (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

 theorem bottStalkCharacter_reciprocity (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    Polynomial.reflect (rankDifference cs x.val (cs.wordProd l)) (bottStalkCharacter cs basis l x.val)=
      ∑ z ∈ lowerFinset cs (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z := by
  apply Polynomial.toLaurent_injective
  let q := OrdinaryR.variableUnit
  have h := HeckeQ.positiveWord_rValue cs q l hl x.val
  have hlen : cs.length x.val≤l.length := hl ▸ length_le_of_bruhat cs x.property.2
  have hp : (↑q⁻¹ : LaurentPolynomial ℤ)^cs.length x.val * (q:LaurentPolynomial ℤ)^l.length=
      (q:LaurentPolynomial ℤ)^(rankDifference cs x.val (cs.wordProd l)) := by
    have he : cs.length (cs.wordProd l)=l.length := hl
    rw [rankDifference,he,← Nat.sub_add_cancel hlen,pow_add]
    calc
      _ = ((↑q⁻¹:LaurentPolynomial ℤ)*(q:LaurentPolynomial ℤ))^cs.length x.val *
          (q:LaurentPolynomial ℤ)^(l.length-cs.length x.val) := by rw [mul_pow]; ring
      _ = _ := by rw [q.inv_mul]; simp
  rw [hp] at h
  have hv (p : Polynomial ℤ) : Polynomial.toLaurent p=
      Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (q:LaurentPolynomial ℤ) p := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [map_add,Polynomial.eval₂_add,hp,hr]
    | monomial n a => simp [q,Polynomial.toLaurent_C_mul_T]
  rw [hv,eval₂_reflect_unit q _ _ (bottStalkCharacter_natDegree_le cs basis l hl x)]
  rw [hv]
  simp only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,OrdinaryR.polynomial_eval,
    bottStalkCharacter_eq_heckeWord,HeckeQ.eval_positiveWord]
  exact h.symm

 theorem bottKernelCharacter_rConvolution (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=
      ∑ z : Interval cs 1 (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z.val*bottStalkCharacter cs basis l z.val := by
  rw [bottKernelCharacter cs basis l hl x,bottStalkCharacter_reciprocity cs basis l hl x]
  exact Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs 1 (cs.wordProd l))))
    (lowerFinset cs (cs.wordProd l))
    (fun z => by simp only [mem_lowerFinset]; exact ⟨fun h => ⟨one_bruhat cs z,h⟩,And.right⟩)
    (fun z => OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z)

end
end KLInvariance.TitsSpace

end


section

/-! Recognition by the actual minimal-boundary object, not by an asserted
character or by restricting a perfect form to an arbitrary summand. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] {hneg : ∀ n < 0, 𝓐 n=⊥}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)
noncomputable section

 theorem top_nontrivial : Nontrivial (B.sheaf.vertex b) := by
  let e := ModuleData.equivOfEq B.top
  let z : ModuleData.unit.{uk,ua,um} hneg := fun _ => (0 : A)
  let o : ModuleData.unit.{uk,ua,um} hneg := fun _ => (1 : A)
  refine ⟨⟨e.symm z,e.symm o,?_⟩⟩
  intro h
  exact zero_ne_one (congrFun (e.symm.injective h) PUnit.unit)

 variable [IsNoetherianRing A] [Fintype V] [Fintype E]

 theorem iso_of_primitive_top_split
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (hb : ∀ x, x≤b) (C : GradedSheaf (𝓐 := 𝓐) G)
    (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCp : (GradedSheaf.Hom.id C).PrimitiveProjector)
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.Iso B.sheaf C) := by
  let := B.top_nontrivial
  obtain ⟨s⟩ := B.splitIn_of_top_split hzero hb C hCq hCfree hCf hCg i p hpi
  exact ⟨s.isoOfPrimitive hCp b⟩

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! The actual symmetric-coefficient BMP boundary sheaf is isomorphic to
its integral adjoint image. The splitting is constructed from the word's
proved free-stalk, exact-edge and flabbiness properties. -/
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

 def bottSplitAdjointSplit : GradedSheaf.SplitIn
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottAdjointSheaf cs basis l hl s.projector).imageSplit
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex)
    (bottAdjointSheaf_edge_idempotent cs basis l hl s.projector s.projector_vertex)

 theorem bottSplitAdjoint_free (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (SymmetricCoefficient (M := M))
      ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex x) := by
  let := symmetricCoefficientNoetherian basis
  let : Module.Free (SymmetricCoefficient (M := M))
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).vertex x) :=
    bottStalkFree cs l x.val
  exact (bottSplitAdjointSplit cs basis l hl B s).vertex_free
    (symmetricGrading_negative basis) (symmetricGrading_zero basis) x

 def bottSplitAdjointTopInclusion : ModuleData.Hom
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  ((bottSplitAdjointSplit cs basis l hl B s).projection.vertex _).comp
    (bottBoundarySheafTopInclusion cs basis l hl B)

 def bottSplitAdjointTopProjection : ModuleData.Hom
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (bottBoundarySheafTopProjection cs basis l hl B).comp
    ((bottSplitAdjointSplit cs basis l hl B s).inclusion.vertex _)

 theorem bottSplitAdjointTop_split
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottSplitAdjointTopProjection cs basis l hl B s).map
      ((bottSplitAdjointTopInclusion cs basis l hl B s).map v)=v := by
  change (bottBoundarySheafTopProjection cs basis l hl B).map
    (((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))=v
  exact (congrArg (bottBoundarySheafTopProjection cs basis l hl B).map
    (bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))).trans
    (bottBoundarySheafTop_split cs basis l hl B v)

 theorem bottBoundarySheaf_iso_adjoint : Nonempty
    (GradedSheaf.Iso B.sheaf (bottSplitAdjointSheaf cs basis l hl B.sheaf s)) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let t := bottSplitAdjointSplit cs basis l hl B s
  exact B.iso_of_primitive_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (t.upperQuotient (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottSplitAdjoint_free cs basis l hl B s)
    (t.flabby (bottProjectionSheaf_flabby cs l hl))
    (t.generated (bottProjectionSheaf_generated cs l 1 (cs.wordProd l)))
    (bottBoundarySplitAdjoint_primitive cs basis l hl _ B s)
    (bottSplitAdjointTopInclusion cs basis l hl B s)
    (bottSplitAdjointTopProjection cs basis l hl B s)
    (bottSplitAdjointTop_split cs basis l hl B s)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.imageSectionEquiv_symm_coordinates (U : Set V)
    (n : B.forget.sections U) (x : V) :
    (((s.imageSectionEquiv U).symm n).val x).val=(s.inclusion.vertex x).map (n.val x) := by
  rw [s.imageSectionEquiv_symm_apply]
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map (n.val x)))=(s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

 theorem SplitIn.imageSectionEquiv_symm_inclusion (U : Set V)
    (n : B.forget.sections U) :
    s.projector.imageInclusion.sectionMap U ((s.imageSectionEquiv U).symm n)=
      s.inclusion.sectionMap U n := by
  apply Subtype.ext
  funext x
  exact s.imageSectionEquiv_symm_coordinates U n x

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The adjoint-summand pairing is the ambient word pairing on its two
honest (generally different) integral sheaf embeddings. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitRightWord (n : B.forget.sections Set.univ) : BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n)).val

 def bottSplitLeftWord
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ) :
    BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m).val

 theorem bottSplitRightWord_coordinates (n : B.forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitRightWord cs basis l hl B s n)=
      (s.inclusion.vertex x).map (n.val x) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv_coordinates cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n) x).trans
      (s.imageSectionEquiv_symm_coordinates Set.univ n x)

 theorem bottSplitLeftWord_coordinates
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitLeftWord cs basis l hl B s m)=(m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact bottImageSectionWordEquiv_coordinates cs basis l hl
    (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m x

 theorem bottSplitAdjointWord_apply
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ) :
    bottSplitAdjointEquivDual cs basis l hl B s m n=
      bottSamelsonDuality cs l (bottSplitLeftWord cs basis l hl B s m)
        (bottSplitRightWord cs basis l hl B s n) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImageEquivDual_apply cs basis l hl s.projector s.projector_vertex m
    ((s.imageSectionEquiv Set.univ).symm n)

end
end KLInvariance.TitsSpace

end


section

/-! An actual recognition isomorphism to the adjoint image gives the required
perfect pairing. The two ambient embeddings remain distinct. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
  (j : GradedSheaf.Iso B (bottSplitAdjointSheaf cs basis l hl B s))
noncomputable section

 def bottRecognizedPerfectPairing : GradedSheaf.PerfectPairing B (l.length : ℤ) where
  pairing := (j.toIso.sections Set.univ).trans (bottSplitAdjointEquivDual cs basis l hl B s)
  homogeneous i q m n hm hn := bottSplitAdjointPairing_homogeneous cs basis l hl B s i q
    (j.toIso.sections Set.univ m) n (fun x => j.vertex_graded x i _ (hm x)) hn
  left_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitLeftWord_coordinates]
      change ((j.vertex y (m.val y)).val)=0
      rw [hm y hy,map_zero]
      rfl
    · rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex x).map (n.val x)=0
      rw [hn]
      exact (s.inclusion.vertex x).map.map_zero
  right_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply,bottSamelson_symmetric]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex y).map (n.val y)=0
      rw [hn y hy]
      exact (s.inclusion.vertex y).map.map_zero
    · rw [bottSplitLeftWord_coordinates]
      change ((j.vertex x (m.val x)).val)=0
      rw [hm,map_zero]
      rfl

end
end KLInvariance.TitsSpace

end


section

/-! The same genuine minimal boundary construction over the symmetric
coefficient algebra. Its polynomial-coordinate comparison is proved separately. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 omit [Fintype σ] in
 theorem symmetric_scalar_mod_positive (a : SymmetricCoefficient (M := M)) :
    ∃ c : ℝ, a-algebraMap ℝ (SymmetricCoefficient (M := M)) c ∈ positiveIdeal (symmetricGrading basis) := by
  obtain ⟨c,hc⟩ := symmetricGrading_zero basis _
    (DirectSum.decompose (symmetricGrading basis) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (symmetricGrading_negative basis)]
  change component (symmetricGrading basis) 0 (a-algebraMap ℝ (SymmetricCoefficient (M := M)) c)=0
  rw [map_sub,hc]
  rw [show component (symmetricGrading basis) 0
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) =
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (symmetricGrading basis) a 0).property]
  exact sub_self _

 theorem symmetricLabel_homogeneous (u b : W) (e : Edge cs u b) :
    symmetricLabel cs u b e ∈ symmetricGrading basis 1 :=
  (mem_symmetricGrading basis 1 _).mpr (polynomialLabel_homogeneous cs u b basis e)

 theorem exists_symmetricBoundarySheaf (b : W) :
    Nonempty (BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  exact MomentGraph.exists_boundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 b) (symmetric_scalar_mod_positive basis)
    ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ (fun x => x.property.2)
    (symmetricLabel cs 1 b) (symmetricLabel_homogeneous cs basis 1 b)

 def symmetricBoundarySheaf (b : W) :
    BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ :=
  (exists_symmetricBoundarySheaf cs basis b).some

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional integral graded support-orthogonal duality for the actual
normalized minimal-boundary sheaf over the symmetric coefficient algebra. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricBoundarySheaf_perfectPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.PerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  obtain ⟨j⟩ := bottBoundarySheaf_iso_adjoint cs basis l hl B s
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨bottRecognizedPerfectPairing cs basis l hl B.sheaf s j⟩

 theorem symmetricBoundarySheaf_perfectPairing (b : W) :
    Nonempty (GradedSheaf.PerfectPairing (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_perfectPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  (hA : ∀ n<0,𝓐 n=⊥) (hB : ∀ n<0,𝓑 n=⊥)
noncomputable section

 def changeUnitHom : Hom (change e he (unit.{uk,ua,um} hA)) (unit hB) where
  map :=
    { toFun m j := e (m.val j)
      map_add' m n := funext fun j => map_add e (m.val j) (n.val j)
      map_smul' b m := by
        funext j
        change e (e.symm b * m.val j)=b * e (m.val j)
        rw [map_mul,e.apply_symm_apply] }
  graded := by
    intro n m hm j
    exact (he (n-0) _).mp ((mem_changePiece e (unit hA) n m).mp hm j)

 def changeUnitInvHom : Hom (unit.{uk,ua,um} hB) (change e he (unit hA)) where
  map :=
    { toFun m := CoefficientChange.mk (fun j => e.symm (m j))
      map_add' m n := CoefficientChange.ext (funext fun j => map_add e.symm (m j) (n j))
      map_smul' b m := by
        apply CoefficientChange.ext
        funext j
        exact map_mul e.symm b (m j) }
  graded := by
    intro n m hm
    apply (mem_changePiece e (unit hA) n _).mpr
    intro j
    apply (he (n-0) _).mpr
    change e (e.symm (m j)) ∈ 𝓑 (n-0)
    rw [e.apply_symm_apply]
    exact hm j

 theorem changeUnitHom_inv (m : unit.{uk,ua,um} hB) :
    (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map m)=m :=
  funext fun j => e.apply_symm_apply (m j)

 theorem changeUnitInvHom_hom (m : change e he (unit.{uk,ua,um} hA)) :
    (changeUnitInvHom e he hA hB).map ((changeUnitHom e he hA hB).map m)=m :=
  CoefficientChange.ext (funext fun j => e.symm_apply_apply (m.val j))

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def unchangeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom (change e he M) (change e he N)) :
    Hom M N where
  map :=
    { toFun m := (f.map (CoefficientChange.mk m)).val
      map_add' m n := congrArg CoefficientChange.val (map_add f.map (CoefficientChange.mk m) (CoefficientChange.mk n))
      map_smul' a m := by
        have hh := congrArg CoefficientChange.val (map_smul f.map (e a) (CoefficientChange.mk m))
        change (f.map (CoefficientChange.mk (e.symm (e a) • m))).val=
          e.symm (e a) • (f.map (CoefficientChange.mk m)).val at hh
        simpa only [e.symm_apply_apply, RingHom.id_apply] using hh }
  graded n m hm := (mem_changePiece e N n _).mp
    (f.graded n (CoefficientChange.mk m) ((mem_changePiece e M n _).mpr hm))

end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def Hom.coefficientUnchange {S T : GradedSheaf (𝓐 := 𝓐) G}
    (g : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he T)) : Hom S T where
  vertex x := ModuleData.unchangeHom e he (g.vertex x)
  edge f := ModuleData.unchangeHom e he (g.edge f)
  lower f m := congrArg CoefficientChange.val (g.lower f (CoefficientChange.mk m))
  upper f m := congrArg CoefficientChange.val (g.upper f (CoefficientChange.mk m))

 theorem coefficientChange_primitive (S : GradedSheaf (𝓐 := 𝓐) G)
    (hS : (Hom.id S).PrimitiveProjector) :
    (Hom.id (GradedSheaf.coefficientChange e he S)).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    let g : Hom S S := f.coefficientUnchange e he
    have hg : g.comp g=g := by
      apply Hom.eq_of_maps
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.vertex x).map (CoefficientChange.mk m)).val) hf
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.edge x).map (CoefficientChange.mk m)).val) hf
    have hgL : g.comp (Hom.id S)=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    have hgR : (Hom.id S).comp g=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    rcases hS.2 g hg hgL hgR with hz | hi
    · left
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hz
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hz
    · right
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hi
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hi

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {M : ModuleData.{uk,ua,um} 𝓐} (hM : M=unit hA)
  {N : ModuleData.{uk,ua,um} 𝓑} (hN : N=unit hB)
noncomputable section

 def changeTopInclusion : Hom N (change e he M) :=
  (changeHom e he (homOfEq hM.symm)).comp
    ((changeUnitInvHom e he hA hB).comp (homOfEq hN))

 def changeTopProjection : Hom (change e he M) N :=
  (homOfEq hN.symm).comp
    ((changeUnitHom e he hA hB).comp (changeHom e he (homOfEq hM)))

 theorem changeTop_split (n : N) :
    (changeTopProjection e he hM hN).map ((changeTopInclusion e he hM hN).map n)=n := by
  subst M
  subst N
  change (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map n)=n
  exact changeUnitHom_inv e he hA hB n

end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  [IsDomain A] [IsDomain B] [IsNoetherianRing B]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (S : BoundarySheaf hA G α b) (T : BoundarySheaf hB G (fun q => e (α q)) b)
noncomputable section

 theorem iso_coefficientChange
    (hzero : ∀ a ∈ 𝓑 0, ∃ c : k, algebraMap k B c=a)
    (hb : ∀ x, x≤b) : Nonempty
      (GradedSheaf.Iso T.sheaf (GradedSheaf.coefficientChange e he S.sheaf)) := by
  exact T.iso_of_primitive_top_split hzero hb (GradedSheaf.coefficientChange e he S.sheaf)
    (GradedSheaf.coefficientChange_upperQuotient e he S.sheaf α S.quotient)
    (GradedSheaf.coefficientChange_free e he S.sheaf S.free)
    (GradedSheaf.coefficientChange_flabby e he S.sheaf S.flabby.flabby)
    (GradedSheaf.coefficientChange_generated e he S.sheaf S.generated)
    (GradedSheaf.coefficientChange_primitive e he S.sheaf S.primitive_identity)
    (ModuleData.changeTopInclusion e he S.top T.top)
    (ModuleData.changeTopProjection e he S.top T.top)
    (ModuleData.changeTop_split e he S.top T.top)

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_perfectPairing :
    Nonempty (GradedSheaf.PerfectPairing
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
  obtain ⟨p⟩ := symmetricBoundarySheaf_perfectPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

 variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]

 theorem sectionDualityObligation : SectionDualityObligation cs b basis := by
  obtain ⟨p⟩ := boundarySheaf_perfectPairing cs b basis
  exact sectionDualityObligation_of_perfectPairing cs b basis p

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

local instance finiteInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _
local instance finiteEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _
local instance (a : Type*) : DecidableEq a := Classical.decEq a

 def boundaryFreeSheaf : FreeSheaf cs 1 b basis where
  sheaf := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf
  free := (boundarySheaf cs 1 b basis (one_bruhat cs b)).free
  quotient := (boundarySheaf cs 1 b basis (one_bruhat cs b)).quotient
  generated := (boundarySheaf cs 1 b basis (one_bruhat cs b)).generated

 def boundaryPerfectPairing : GradedSheaf.PerfectPairing
    (boundaryFreeSheaf cs b basis).sheaf (cs.length b : ℤ) :=
  (boundarySheaf_perfectPairing cs b basis).some

 def boundaryFreeDuality : FreeSheaf.SectionDuality cs 1 b basis (boundaryFreeSheaf cs b basis) :=
  FreeSheaf.dualityOfPairing cs 1 b basis _ (boundaryPerfectPairing cs b basis)

 theorem boundaryKernelFree (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (boundaryFreeSheaf cs b basis).sheaf x) :=
  FreeSheaf.kernel_free cs b basis _ (boundaryFreeDuality cs b basis) x

 def costalkCharacter (x : Interval cs 1 b) : Polynomial ℤ :=
  GradedSheaf.freeKernelChar (boundaryFreeSheaf cs b basis).sheaf (boundaryKernelFree cs b basis) x

 theorem costalkCharacter_reflect (x : Interval cs 1 b) :
    costalkCharacter cs b basis x=Polynomial.reflect (rankDifference cs x.val b)
      (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
  apply FreeSheaf.kernel_character cs b basis _ (boundaryFreeDuality cs b basis) (cs.length b) _ le_rfl x
  intro i j m a hm ha
  exact (boundaryPerfectPairing cs b basis).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

 theorem stalkBasis_degree_le (x : Interval cs 1 b)
    (c : NonnegativeBasis (σ := σ)
      ((boundaryFreeSheaf cs b basis).sheaf.vertex x).piece) (i : c.index) :
    c.degree i≤rankDifference cs x.val b := by
  apply ModuleData.degree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs b basis _ (boundaryFreeDuality cs b basis) x)
    (rankDifference cs x.val b) _ c i
  exact FreeSheaf.kernelDual_homogeneous cs b basis _ (boundaryFreeDuality cs b basis)
    (cs.length b) (fun i j m a hm ha => (boundaryPerfectPairing cs b basis).homogeneous i j m a
      (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x)))
    x (length_le_of_bruhat cs x.property.2)

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Set V} {hK : IsLowerSet K}

omit [IsNoetherianRing A] in
 theorem lowerExtend_kernel_iff (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (m : B.lowerExtend.vertex x.val) :
    m∈B.lowerExtend.upwardSubmodule x.val Set.univ ↔
      B.lowerExtendVertex x m∈B.upwardSubmodule x Set.univ := by
  constructor
  · intro hm e _
    rcases e with ⟨⟨e,he⟩,hx⟩
    cases hx
    have hh := hm ⟨e,rfl⟩ (Set.mem_univ _)
    exact congrFun hh ⟨⟨he⟩⟩
  · intro hm e _
    rcases x with ⟨x,hx⟩
    rcases e with ⟨e,he⟩
    change G.source e=x at he
    subst x
    apply funext
    intro h
    have hh := hm ⟨⟨e,h.down.down⟩,rfl⟩ (Set.mem_univ _)
    exact hh

 def lowerExtendKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) : kernelData B.lowerExtend x.val ≃ₗ[A] kernelData B x where
  toFun m := ⟨B.lowerExtendVertex x m.val,(lowerExtend_kernel_iff B x m.val).mp m.property⟩
  invFun m := ⟨(B.lowerExtendVertex x).symm m.val,(lowerExtend_kernel_iff B x _).mpr (by
    simpa only [LinearEquiv.apply_symm_apply] using m.property)⟩
  left_inv m := Subtype.ext ((B.lowerExtendVertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((B.lowerExtendVertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (B.lowerExtendVertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (B.lowerExtendVertex x) a m.val)

 theorem lowerExtendKernelEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (n : ℤ) (m : kernelData B.lowerExtend x.val)
    (hm : m∈(kernelData B.lowerExtend x.val).piece n) :
    B.lowerExtendKernelEquiv x m∈(kernelData B x).piece n :=
  B.lowerExtendVertex_graded x n m.val hm

omit [IsNoetherianRing A] in
 theorem fullKernel_pullback (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    (B.pullback f).upwardSubmodule x Set.univ=B.upwardSubmodule (f.vertex x) Set.univ := by
  exact B.forget.pullback_kernel f x Set.univ Set.univ
    (fun e he => (he (Set.mem_univ e)).elim) (fun e _ he => hlift e x he)

 def pullbackKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    kernelData (B.pullback f) x ≃ₗ[A] kernelData B (f.vertex x) where
  toFun m := ⟨m.val,fullKernel_pullback B f hlift x ▸ m.property⟩
  invFun m := ⟨m.val,(fullKernel_pullback B f hlift x).symm ▸ m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem pullbackKernelEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V)
    (n : ℤ) (m : kernelData (B.pullback f) x) (hm : m∈(kernelData (B.pullback f) x).piece n) :
    B.pullbackKernelEquiv f hlift x m∈(kernelData B (f.vertex x)).piece n := hm

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 def lowerKernelEquiv (c x : Interval cs 1 b) (hx : x≤c) :
    GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩ :=
  ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv ⟨x,hx⟩).trans
    ((boundaryFreeSheaf cs c.val basis).sheaf.pullbackKernelEquiv
      (lowerIntervalMap cs b c) (lowerIntervalMap_outgoing cs b c) ⟨x,hx⟩)

 theorem lowerKernelEquiv_graded (c x : Interval cs 1 b) (hx : x≤c)
    (n : ℤ) (v : GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x)
    (hv : v∈(GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x).piece n) :
    lowerKernelEquiv cs b basis c x hx v∈(GradedSheaf.kernelData
      (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩).piece n :=
  (lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv_graded ⟨x,hx⟩ n v hv

 theorem boundaryModels_kernelFree (c x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) := by
  by_cases hx : x≤c
  · let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact Module.Free.of_equiv (lowerKernelEquiv cs b basis c x hx).symm
  · let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance

 theorem boundaryModels_kernelCharacter (c x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar ((boundaryModels cs b basis).sheaf c)
      (boundaryModels_kernelFree cs b basis c) x=
      Polynomial.reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x) := by
  let := boundaryModels_kernelFree cs b basis c x
  by_cases hx : x≤c
  · rw [lowerCharacter,dite_eq_left hx,← costalkCharacter_reflect cs c.val basis ⟨x.val,x.property.1,hx⟩]
    let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (lowerKernelEquiv cs b basis c x hx)
      (lowerKernelEquiv_graded cs b basis c x hx)
  · rw [lowerCharacter,dite_eq_right hx,Polynomial.reflect_zero]
    let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ModuleData.char_zero _

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 theorem exists_character_decomposition [Fintype V] [Fintype E]
    {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x))
    (hkb : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x))
    (hq : B.UpperQuotient α) (hfl : B.forget.Flabby) (hg : B.forget.Generated) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B hf x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B hkb x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  obtain ⟨C,hC,⟨j⟩⟩ := exists_modelSumIso (polynomialGrading_zero k σ) O B hf hq hfl hg
  obtain ⟨m,hm,heq,hkeq⟩ := hC.character_both O hk
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · rw [← heq x]
    let _ := hf x
    let _ := hC.free O x
    exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)
  · rw [← hkeq x]
    let _ := hkb x
    let _ := hC.kernelFree hk x
    exact ModuleData.character_eq_of_gradedEquiv (j.kernelEquiv x) (j.kernelEquiv_graded x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottCharacter_decomposition_both (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x) ∧
      (∀ x, GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
        (bottKernelFree cs basis l hl) x=
        ∑ y, m y*Polynomial.reflect (rankDifference cs x.val y.val)
          (lowerCharacter cs (cs.wordProd l) basis y x)) := by
  classical
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  obtain ⟨m,hm,he,hk⟩ := GradedSheaf.exists_character_decomposition
    (boundaryModels cs (cs.wordProd l) basis) (boundaryModels_kernelFree cs (cs.wordProd l) basis)
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)) (bottKernelFree cs basis l hl)
    (bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_flabby cs basis l hl) (bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l))
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · simpa only [bottPolynomialSheaf_character,boundaryModels_character] using he x
  · simpa only [boundaryModels_kernelCharacter] using hk x

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
noncomputable section

 def unitPolynomialBasis : NonnegativeBasis (σ := σ)
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).piece where
  index := PUnit.{max uk us um + 1}
  finite := inferInstance
  basis := Pi.basisFun (MvPolynomial σ k) _
  degree _ := 0
  homogeneous i := by
    intro j
    change (Pi.basisFun (MvPolynomial σ k) _ i) j ∈ polynomialGrading k σ (0-0)
    cases i
    cases j
    simpa using SetLike.one_mem_graded (polynomialGrading k σ)

 theorem char_unit :
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).char=1 := by
  rw [char,character_eq _ _ (unitPolynomialBasis (k := k) (σ := σ))]
  change (∑ i : PUnit.{max uk us um + 1}, (X : Polynomial ℤ)^0)=1
  simp

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem stalkCharacter_top :
    stalkCharacter cs 1 b basis (one_bruhat cs b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=1 := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
  change (B.sheaf.vertex ⟨b,one_bruhat cs b,bruhat_refl cs b⟩).char=1
  exact (ModuleData.character_eq_of_gradedEquiv (ModuleData.equivOfEq B.top)
    (ModuleData.equivOfEq_graded B.top)).trans ModuleData.char_unit

 theorem lowerCharacter_diagonal (c : Interval cs 1 b) : lowerCharacter cs b basis c c=1 := by
  rw [lowerCharacter,dite_eq_left le_rfl]
  exact stalkCharacter_top cs c.val basis

 theorem lowerCharacter_at_top (c : Interval cs 1 b) :
    lowerCharacter cs b basis c ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=
      if c.val=b then 1 else 0 := by
  by_cases hc : c.val=b
  · have he : c=⟨b,one_bruhat cs b,bruhat_refl cs b⟩ := Subtype.ext hc
    rw [ite_eq_left hc,←he,lowerCharacter_diagonal]
  · rw [ite_eq_right hc]
    apply lowerCharacter_zero
    intro h
    exact hc (bruhat_antisymm cs c.property.2 h)

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance lowerConvInterval (c : W) : Fintype (Interval cs 1 c) := by
  let := interval_finite cs 1 c
  exact Fintype.ofFinite _

 def lowerIntervalEquiv (c : Interval cs 1 b) : Set.Iic c ≃ Interval cs 1 c.val where
  toFun := (lowerIntervalMap cs b c).vertex
  invFun z := ⟨⟨z.val,z.property.1,bruhat_trans cs z.property.2 c.property.2⟩,z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem lowerCharacter_convolution (c x : Interval cs 1 b) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=
      ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z := by
  classical
  let f (z : Interval cs 1 b) := OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z
  have hf : ∀ z : Interval cs 1 b, ¬z≤c → f z=0 := by
    intro z hz
    simp only [f,lowerCharacter_zero cs b basis c z hz,mul_zero]
  have he : (∑ z : Interval cs 1 b, f z) = ∑ z ∈ Finset.univ.filter (fun z => z≤c), f z := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z _ hz
    exact hf z (by simpa using hz)
  change (∑ z, f z)=_
  rw [he,Finset.sum_subtype (p := fun z : Interval cs 1 b => z≤c) _ (by simp)]
  calc
    _ = ∑ z : Set.Iic c, OrdinaryR.polynomial cs x.val z.val.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) ((lowerIntervalEquiv cs b c) z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [f,lowerCharacter,dite_eq_left z.property]
      rfl
    _ = _ := Equiv.sum_comp (lowerIntervalEquiv cs b c) (fun z => OrdinaryR.polynomial cs x.val z.val*
      stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)

 theorem lowerCharacter_convolution_zero (c x : Interval cs 1 b) (hx : ¬x≤c) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=0 := by
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z≤c
  · rw [OrdinaryR.polynomial_zero cs x.val z.val (fun h => hx (bruhat_trans cs h hz)),zero_mul]
  · rw [lowerCharacter_zero cs b basis c z hz,mul_zero]

 theorem lowerCharacter_reciprocity_lift (c : Interval cs 1 b)
    (h : ∀ x : Interval cs 1 c.val,
      reflect (rankDifference cs x.val c.val) (stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) x)=
        ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
          stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)
    (x : Interval cs 1 b) :
      reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x)=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z := by
  by_cases hx : x≤c
  · rw [lowerCharacter_convolution,lowerCharacter,dite_eq_left hx]
    exact h ⟨x.val,x.property.1,hx⟩
  · rw [lowerCharacter_zero cs b basis c x hx,reflect_zero,lowerCharacter_convolution_zero cs b basis c x hx]

end
end KLInvariance.BruhatGraph

end


section

/-! Finite unipotent character cancellation. The transition data is actually
constructed for word/BMP sheaves; this lemma assumes only the displayed
linear identities and cannot supply the KL degree bound. -/

end

end OAI
