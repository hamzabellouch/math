import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit

namespace OAI

noncomputable section

noncomputable section

open Filter

open scoped InnerProductSpace ComplexOrder Topology BigOperators

namespace Kadison.ProjectionBlocks

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : ι → H →L[ℂ] H) (hp : ∀ i,IsStarProjection (P i))
    (ho : ∀ i j,i≠j → P i*P j=0)

def space : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ i : ι,∃ ξ : H,P i ξ=x}).topologicalClosure

instance space_complete : CompleteSpace (space P) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def finiteSum (s : Finset ι) : H →L[ℂ] H := ∑ i∈s,P i

omit [CompleteSpace H] in
lemma generator_mem (i : ι) (x : H) : P i x∈space P :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,x,rfl⟩)

include hp ho in
lemma finiteSum_projection (s : Finset ι) : IsStarProjection (finiteSum P s) := by
  classical
  constructor
  · change (∑ i∈s,P i)*(∑ i∈s,P i)=∑ i∈s,P i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (hp i).isIdempotentElem.eq
    · intro j hj hji
      exact ho i j hji.symm
  · change star (∑ i∈s,P i)=∑ i∈s,P i
    rw [star_sum]
    exact Finset.sum_congr rfl (fun i _ => (hp i).isSelfAdjoint.star_eq)

include hp ho in
lemma finiteSum_mul (s : Finset ι) {i : ι} (hi : i∈s) : finiteSum P s*P i=P i := by
  classical
  rw [finiteSum,Finset.sum_mul,Finset.sum_eq_single_of_mem i hi]
  · exact (hp i).isIdempotentElem.eq
  · intro j hj hji
    exact ho j i hji

include hp ho in
lemma finiteSum_tendsto_space {x : H} (hx : x∈space P) :
    Tendsto (fun s : Finset ι => finiteSum P s x) atTop (𝓝 x) := by
  classical
  have hg (i : ι) (x : H) : Tendsto (fun s : Finset ι => finiteSum P s (P i x)) atTop (𝓝 (P i x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i}:Finset ι)] with s hs
    exact (congrArg (fun T : H →L[ℂ] H => T x)
      (finiteSum_mul P hp ho s (hs (by simp)))).symm
  have hspan : ∀ y∈Submodule.span ℂ {x | ∃ i : ι,∃ ξ : H,P i ξ=x},
      Tendsto (fun s : Finset ι => finiteSum P s y) atTop (𝓝 y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i,ξ,rfl⟩ := hy; exact hg i ξ
    | zero => simpa only [map_zero] using (tendsto_const_nhds (x:=(0:H)) (f:=atTop (α:=Finset ι)))
    | add x y hx hy hxlim hylim => simpa only [map_add] using hxlim.add hylim
    | smul c x hx hxlim => simpa only [map_smul] using hxlim.const_smul c
  have hnorm (s : Finset ι) : ‖finiteSum P s‖≤1 := (finiteSum_projection P hp ho s).norm_le _
  have hequi : Equicontinuous (fun s : Finset ι => fun x : H => finiteSum P s x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun s =>
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (hnorm s))).equicontinuous
  exact (hequi x).tendsto_of_mem_closure
    (continuous_id.continuousAt.mono_left inf_le_left) hspan hx

lemma projection_left (i : ι) : (space P).starProjection*P i=P i := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (generator_mem P i x)

include hp in
lemma projection_right (i : ι) : P i*(space P).starProjection=P i := by
  have he := congrArg star (projection_left P i)
  simpa only [star_mul,(hp i).isSelfAdjoint.star_eq,
    (isSelfAdjoint_starProjection (space P)).star_eq] using he

include hp ho in
lemma finiteSum_tendsto (x : H) :
    Tendsto (fun s : Finset ι => finiteSum P s x) atTop (𝓝 ((space P).starProjection x)) := by
  have hh := finiteSum_tendsto_space P hp ho ((space P).starProjection_apply_mem x)
  have he (s : Finset ι) : finiteSum P s*((space P).starProjection)=finiteSum P s := by
    rw [finiteSum,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => projection_right P hp i)
  have hev (s : Finset ι) : finiteSum P s ((space P).starProjection x)=finiteSum P s x :=
    congrArg (fun T : H →L[ℂ] H => T x) (he s)
  simpa only [hev] using hh

omit [CompleteSpace H] in
lemma invariant (T : H →L[ℂ] H) (ht : ∀ i,T*P i=P i*T) :
    ∀ x∈space P,T x∈space P := by
  intro x hx
  apply closure_minimal (t := {x | T x∈space P}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage T.continuous) hx
  apply (Submodule.span_le.mpr ?_ : Submodule.span ℂ _≤(space P).comap T.toLinearMap)
  rintro y ⟨i,ξ,rfl⟩
  change T (P i ξ)∈space P
  rw [show T (P i ξ)=P i (T ξ) from congrArg (fun S : H →L[ℂ] H => S ξ) (ht i)]
  exact generator_mem P i (T ξ)

include hp in
lemma projection_commutes (T : H →L[ℂ] H) (ht : ∀ i,T*P i=P i*T) :
    (space P).starProjection*T=T*(space P).starProjection := by
  apply projection_commutes_of_invariant (space P) T (invariant P T ht)
  apply invariant P (star T)
  intro i
  have he := congrArg star (ht i)
  simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using he.symm

include hp ho in
lemma inner_blocks (i j : ι) (hij : i≠j) (x y : H) : inner ℂ (P i x) (P j y)=0 := by
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x ((star (P i)*P j) y)=0
  rw [(hp i).isSelfAdjoint.star_eq,ho i j hij]
  simp

omit [CompleteSpace H] in
lemma norm_sum_sq (v : ι → H) (hv : ∀ i j,i≠j → inner ℂ (v i) (v j)=0) (s : Finset ι) :
    ‖∑ i∈s,v i‖^2=∑ i∈s,‖v i‖^2 := by
  classical
  have hh : inner ℂ (∑ i∈s,v i) (∑ i∈s,v i)=∑ i∈s,inner ℂ (v i) (v i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum,Finset.sum_eq_single_of_mem i hi]
    intro j hj hji
    exact hv i j hji.symm
  simp_rw [@norm_sq_eq_re_inner ℂ]
  change Complex.re (inner ℂ (∑ i∈s,v i) (∑ i∈s,v i))=∑ i∈s,Complex.re (inner ℂ (v i) (v i))
  rw [hh]
  simp

include hp ho in
theorem norm_le_of_blocks (T : H →L[ℂ] H) {c : ℝ} (hc : 0≤c)
    (ht : ∀ i,T*P i=P i*T)
    (hb : ∀ i x,‖T (P i x)‖≤c*‖P i x‖)
    (hfull : (space P).starProjection=1) : ‖T‖≤c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hT (i j : ι) (hij : i≠j) : inner ℂ (T (P i x)) (T (P j x))=0 := by
    have he (i : ι) : T (P i x)=P i (T x) := congrArg (fun S : H →L[ℂ] H => S x) (ht i)
    rw [he,he]
    exact inner_blocks P hp ho i j hij _ _
  have hs (s : Finset ι) : ‖T (finiteSum P s x)‖≤c*‖finiteSum P s x‖ := by
    have he : finiteSum P s x=∑ i∈s,P i x := by simp [finiteSum]
    rw [he,map_sum]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
    rw [norm_sum_sq _ hT,mul_pow,norm_sum_sq _ (fun i j hij => inner_blocks P hp ho i j hij x x),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr (hb i x)
  have hlim : Tendsto (fun s : Finset ι => finiteSum P s x) atTop (𝓝 x) := by
    simpa only [hfull,one_apply_eq_self] using finiteSum_tendsto P hp ho x
  exact le_of_tendsto_of_tendsto ((T.continuous.tendsto x).comp hlim).norm
    (hlim.norm.const_mul c) (Filter.Eventually.of_forall hs)

end Kadison.ProjectionBlocks
end
end

end OAI
