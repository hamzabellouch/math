import Mathlib
import OAI.Analysis.Commutator.HilbertSequence
import OAI.Analysis.Commutator.LittleGrothendieck

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.LittleGrothendieck

open HilbertSequence

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def sequenceLinear (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    (ℕ →ᵇ A) →ₗ[ℂ] Pre ω E where
  toFun x := ⟨T.compLeftContinuousBounded ℕ x⟩
  map_add' x y := by
    apply (equiv ω E).injective
    exact map_add (T.compLeftContinuousBounded ℕ) x y
  map_smul' z x := by
    apply (equiv ω E).injective
    exact map_smul (T.compLeftContinuousBounded ℕ) z x

@[simp] lemma sequenceLinear_seq (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    (x : ℕ →ᵇ A) (n : ℕ) : (sequenceLinear ω T x).seq n=T (x n) := rfl

lemma sequenceLinear_bound (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : ℕ →ᵇ A) :
    ‖sequenceLinear ω T x‖≤‖T‖*‖x‖ := by
  apply le_of_tendsto (tendsto_norm ω E (sequenceLinear ω T x))
  exact Filter.Eventually.of_forall (fun n => (T.le_opNorm (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm n) (norm_nonneg _)))

def sequenceMap (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    (ℕ →ᵇ A) →L[ℂ] Space ω E :=
  (toComplₗᵢ : Pre ω E →ₗᵢ[ℂ] Space ω E).toContinuousLinearMap.comp
    ((sequenceLinear ω T).mkContinuous ‖T‖ (sequenceLinear_bound ω T))

@[simp] lemma sequenceMap_apply (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    (x : ℕ →ᵇ A) : sequenceMap ω T x=(sequenceLinear ω T x : Space ω E) := rfl

lemma sequenceMap_norm_le (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    ‖sequenceMap ω T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [sequenceMap_apply, Completion.norm_coe]
  exact sequenceLinear_bound ω T x

lemma sequenceMap_norm_tendsto (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : ℕ →ᵇ A) :
    Tendsto (fun n => ‖T (x n)‖) (ω : Filter ℕ) (𝓝 ‖sequenceMap ω T x‖) :=
  norm_coe_tendsto ω E (sequenceLinear ω T x)

lemma sequenceMap_const (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : A) :
    sequenceMap ω T (BoundedContinuousFunction.const ℕ x)=constant ω E (T x) := rfl

lemma unitary_norm_le_one (u : unitary A) : ‖(u:A)‖≤1 := by
  cases subsingleton_or_nontrivial A with
  | inl h => simpa only [Subsingleton.elim (u:A) 0,norm_zero] using (zero_le_one : (0:ℝ)≤1)
  | inr h => exact le_of_eq (CStarRing.norm_coe_unitary u)

theorem exists_sequence_unitary_max (T : A →L[ℂ] E) :
    ∃ (ω : Ultrafilter ℕ) (u : unitary (ℕ →ᵇ A)),
      ∀ v : unitary (ℕ →ᵇ A), ‖sequenceMap ω T (v:ℕ →ᵇ A)‖ ≤
        ‖sequenceMap ω T (u:ℕ →ᵇ A)‖ := by
  classical
  let S : Set ℝ := range (fun u : unitary A => ‖T (u:A)‖)
  have hSne : S.Nonempty := ⟨‖T (1:A)‖,1,rfl⟩
  have hSb : BddAbove S := ⟨‖T‖,by
    rintro r ⟨u,rfl⟩
    exact (T.le_opNorm _).trans (by nlinarith [unitary_norm_le_one u, norm_nonneg T])⟩
  obtain ⟨r,_,hr,hmem⟩ := exists_seq_tendsto_sSup hSne hSb
  choose u hu using hmem
  let U : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (u n:A)) 1 (fun n => unitary_norm_le_one (u n))
  have hU : U ∈ unitary (ℕ →ᵇ A) := by
    constructor <;> apply BoundedContinuousFunction.ext <;> intro n
    · exact Unitary.coe_star_mul_self (u n)
    · exact Unitary.coe_mul_star_self (u n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  have hlim : ‖sequenceMap ω T U‖=sSup S := by
    apply tendsto_nhds_unique (sequenceMap_norm_tendsto ω T U)
    change Tendsto (fun n => ‖T (u n:A)‖) (ω : Filter ℕ) (𝓝 (sSup S))
    simpa only [hu] using hr.mono_left hω
  refine ⟨ω,⟨U,hU⟩,fun v => ?_⟩
  rw [show (⟨U,hU⟩ : unitary (ℕ →ᵇ A)).val=U from rfl,hlim]
  apply le_of_tendsto (sequenceMap_norm_tendsto ω T (v:ℕ →ᵇ A))
  apply Filter.Eventually.of_forall
  intro n
  have hv : (v:ℕ →ᵇ A) n ∈ unitary A := by
    constructor
    · exact congrArg (fun f : ℕ →ᵇ A => f n) (Unitary.coe_star_mul_self v)
    · exact congrArg (fun f : ℕ →ᵇ A => f n) (Unitary.coe_mul_star_self v)
  exact le_csSup hSb ⟨⟨(v:ℕ →ᵇ A) n,hv⟩,rfl⟩

theorem sum_norm_sq_le {ι : Type*} [Fintype ι] (T : A →L[ℂ] E) (a : ι → A) :
    ∑ i, ‖T (a i)‖^2 ≤ ‖T‖^2*(‖∑ i, star (a i)*a i‖+‖∑ i, a i*star (a i)‖) := by
  classical
  obtain ⟨ω,u,hu⟩ := exists_sequence_unitary_max T
  have h := sum_sq_le_at_unitary_max (sequenceMap ω T) u hu
    (fun i => BoundedContinuousFunction.const ℕ (a i))
  simp only [sequenceMap_const, LinearIsometry.norm_map] at h
  have hc : (∑ i, star (BoundedContinuousFunction.const ℕ (a i))*
      BoundedContinuousFunction.const ℕ (a i))=
      BoundedContinuousFunction.const ℕ (∑ i, star (a i)*a i) := by
    ext n
    simp
  have hr : (∑ i, BoundedContinuousFunction.const ℕ (a i)*
      star (BoundedContinuousFunction.const ℕ (a i)))=
      BoundedContinuousFunction.const ℕ (∑ i, a i*star (a i)) := by
    ext n
    simp
  rw [hc,hr,BoundedContinuousFunction.norm_const_eq,BoundedContinuousFunction.norm_const_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (sequenceMap_norm_le ω T) 2)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)))

end Kadison.LittleGrothendieck

end

end
end

end OAI
