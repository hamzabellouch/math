import OAI.Analysis.Steinitz.Transference

namespace OAI

/-! The Euclidean Steinitz–Bergström theorem with one absolute constant. -/

section

open Matrix GaussianTail MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise
namespace EuclideanSteinitz.Filter
open GaussianAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma filtered_signed_prefixes {n : ℕ} (b : Fin n → ι → ℝ)
    (hb : ∀ i, vectorMass (b i) ≤ signingScale^2) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
      ∀ k : ℕ, k ≤ n →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), ε i • WithLp.toLp 2 (b i)‖ ≤
          (2*bodyScale*stateRadius)*Real.sqrt (Fintype.card ι) := by
  let R := initialMatrix ι (Fin n)
  let L := familySteps b
  let ps : Fin (n+1) → List (Step ι (ι⊕Fin n)) := fun t => L.take t.val
  let H := normalizedPredictor b
  let K := bodyScale • applicationDomain (fun t => run R (ps t)) H
  have hlt : ∀ i,vectorMass (b i)<1 := fun i =>
    (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  have hg : ShiftedSections.Good K := applicationDomain_good initialMatrix_coisometry
    (familySteps_good hlt) (familySteps_fresh b) (familySteps_nodup b) ps
    (fun t => List.take_prefix t.val L) H (normalizedPredictor_mass hb) (normalizedPredictor_column hb)
  let m : Fin n → EuclideanSpace ℝ (ι⊕Fin n) →L[ℝ] ℝ := fun i => rowMap (familyPredictor b i)
  have hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (Sum.inr l) 1)=0 := by
    intro i l hil
    rw [show m i=rowMap (familyPredictor b i) from rfl,rowMap_single,familyPredictor_future b i l hil]
  have hslab : ∀ x∈K,∀ i,|m i x|<1/4 := by
    intro x hx i
    obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
    have hh := hy.2 i
    change ‖matrixMap (normalizedPredictor b i) y‖<2*slabRadius at hh
    rw [normalizedPredictor_norm] at hh
    have hh' := (div_lt_iff₀ signingScale_pos).mp hh
    change |rowMap (familyPredictor b i) (bodyScale • y)| < _
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos bodyScale_pos]
    have hf := mul_lt_mul_of_pos_left hh' bodyScale_pos
    have he : bodyScale*(2*slabRadius*signingScale)=1/4 := by
      nlinarith [signingScale_cancel]
    simpa only [he] using hf
  obtain ⟨ε,x,hε,hx,hxout,hxeq⟩ := ShiftedSections.adaptive_linear_equations
    (Sum.inr : Fin n → ι⊕Fin n) Sum.inr_injective m hm hg hslab
  have hx0 : ∀ i,x (Sum.inl i)=0 := by
    intro i
    exact hxout (Sum.inl i) (fun j => Sum.inl_ne_inr)
  have hxeq' : ∀ i,x (Sum.inr i)=rowMap (rawRow (run R (L.take i.val)) (b i)) x+ε i := by
    intro i
    have hh := hxeq i
    change x (Sum.inr i)=rowMap (familyPredictor b i) x+ε i at hh
    rw [familyPredictor_form,noiseRow_eval _ _ hx0] at hh
    exact hh
  have hcancel (k : ℕ) : matrixMap (run R (L.take k)) x=
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),ε i • WithLp.toLp 2 (b i) := by
    have hh := run_prefix_cancel (fun i => symmetricStep (b i) (Sum.inr i)) R x ε
      (fun _ => rfl) hxeq' k
    rw [initialMatrix_eval x hx0,zero_add,EuclideanSteinitzBergstrom.sum_take_ofFn] at hh
    exact hh
  refine ⟨ε,hε,fun k hk => ?_⟩
  rw [← hcancel k]
  obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
  have hh := hy.1.1 (⟨k,by omega⟩ : Fin (n+1))
  change ‖matrixMap (run R (L.take k)) y‖ < 2*stateRadius*Real.sqrt (Fintype.card ι) at hh
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos bodyScale_pos]
  have hf := mul_lt_mul_of_pos_left hh bodyScale_pos
  nlinarith

end EuclideanSteinitz.Filter

namespace EuclideanSteinitzBergstrom
open EuclideanSteinitz.Filter GaussianAR

noncomputable def universalConstant : ℝ := 2*bodyScale*stateRadius/signingScale

theorem signed_prefix_bound : SignedPrefixBound universalConstant := by
  classical
  intro d N hd _hN v hv
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  let b : Fin N → Fin d → ℝ := fun i => (signingScale • v i).ofLp
  have hb : ∀ i,vectorMass (b i) ≤ signingScale^2 := by
    intro i
    have he : vectorMass (b i)=‖signingScale • v i‖^2 := by
      exact (EuclideanSpace.real_norm_sq_eq (signingScale • v i)).symm
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos signingScale_pos,mul_pow]
    exact (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (v i),hv i] : ‖v i‖^2≤1)
      (sq_nonneg signingScale)).trans_eq (mul_one _)
  obtain ⟨ε,hε,hpref⟩ := filtered_signed_prefixes b hb
  refine ⟨ε,hε,fun k hk => ?_⟩
  have hh := hpref k hk
  have he : (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),ε i • WithLp.toLp 2 (b i))=
      signingScale • ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),ε i • v i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ε i • (signingScale • v i)=signingScale • (ε i • v i)
    exact smul_comm _ _ _
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos signingScale_pos,Fintype.card_fin] at hh
  have hc : universalConstant*Real.sqrt d=(2*bodyScale*stateRadius*Real.sqrt d)/signingScale := by
    unfold universalConstant
    ring
  rw [hc]
  apply (le_div_iff₀ signingScale_pos).mpr
  nlinarith

theorem main : ∃ C : ℝ, SignedPrefixBound C ∧ OrderingPrefixBound C :=
  ⟨universalConstant,signed_prefix_bound,signing_implies_ordering universalConstant signed_prefix_bound⟩

end EuclideanSteinitzBergstrom

end

end OAI
