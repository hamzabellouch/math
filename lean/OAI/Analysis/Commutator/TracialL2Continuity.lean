import Mathlib
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma trace_star (a : A) : τ (star a)=star (τ a) := by
  have h := inner_conj_symm (𝕜:=ℂ) (τ.toPreGNS a) (τ.toPreGNS 1)
  change star (τ (star (1:A)*a))=τ (star a*1) at h
  simpa only [star_one,one_mul,mul_one] using h.symm

lemma norm_trace_star (a : A) : ‖τ (star a)‖=‖τ a‖ := by
  rw [trace_star,_root_.norm_star]

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_trace_star_mul (a b : A) : ‖τ (star a*b)‖=‖τ (a*star b)‖ := by
  rw [←norm_trace_star τ (star a*b),star_mul,star_star,hτ]

include hτ in
lemma norm_mul_sub_mul (a b c d : A) :
    norm τ (a*b-c*d) ≤ norm τ (a-c)*‖b‖+‖c‖*norm τ (b-d) := by
  have he : a*b-c*d=(a-c)*b+c*(b-d) := by noncomm_ring
  rw [he]
  exact (norm_add τ _ _).trans
    (add_le_add (norm_mul_right τ hτ _ _) (norm_mul_left τ _ _))

lemma norm_one (hone : τ 1=1) : norm τ (1:A)=1 := by
  have hh := norm_sq τ (1:A)
  simp only [star_one,mul_one,hone,Complex.one_re] at hh
  nlinarith [norm_nonneg τ (1:A)]

include hτ in
lemma norm_trace_le (hone : τ 1=1) (a : A) : ‖τ a‖ ≤ norm τ a := by
  simpa only [mul_one,norm_one τ hone] using norm_trace_mul τ hτ a 1

include hτ in
lemma norm_pow_sub_pow (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    norm τ (a^n-b^n) ≤ (n:ℝ)*norm τ (a-b) := by
  induction n with
  | zero => simp [norm]
  | succ n ih =>
    have hbn : ‖b^n‖ ≤ 1 := by
      cases n with
      | zero => simpa only [pow_zero] using (IsStarProjection.one A).norm_le 1
      | succ n =>
        exact (norm_pow_le' b (Nat.succ_pos n)).trans
          (pow_le_one₀ (_root_.norm_nonneg _) hb)
    calc
      _=norm τ (a^n*a-b^n*b) := by rw [pow_succ,pow_succ]
      _ ≤ norm τ (a^n-b^n)*‖a‖+‖b^n‖*norm τ (a-b) := norm_mul_sub_mul τ hτ _ _ _ _
      _ ≤ (n:ℝ)*norm τ (a-b)+norm τ (a-b) := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_left ha (norm_nonneg τ _)).trans (by simpa using ih))
          (mul_le_of_le_one_left (norm_nonneg τ _) hbn)
      _=_ := by rw [Nat.cast_succ]; ring

lemma tendsto_of_norm_sub_le {ι : Type*} {l : Filter ι} (f : ι → A) (a : A)
    (b : ι → ℝ) (hb : Tendsto b l (𝓝 0)) (h : ∀ i,norm τ (f i-a) ≤ b i) :
    Tendsto (fun i => norm τ (f i-a)) l (𝓝 0) :=
  squeeze_zero (fun index => norm_nonneg τ (f index-a)) h hb

include hτ in
lemma tendsto_mul {ι : Type*} {l : Filter ι} {a b : ι → A} {x y : A}
    (ha : Tendsto (fun i => norm τ (a i-x)) l (𝓝 0))
    (hb : Tendsto (fun i => norm τ (b i-y)) l (𝓝 0))
    {B : ℝ} (hB : ∀ i,‖b i‖ ≤ B) :
    Tendsto (fun i => norm τ (a i*b i-x*y)) l (𝓝 0) := by
  have hh := (ha.mul_const B).add (hb.const_mul ‖x‖)
  simp only [zero_mul,mul_zero,add_zero] at hh
  exact squeeze_zero (fun i => norm_nonneg τ _) (fun i =>
    (norm_mul_sub_mul τ hτ _ _ _ _).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hB i) (norm_nonneg τ _)) le_rfl)) hh

include hτ in
lemma tendsto_trace {ι : Type*} {l : Filter ι} {a : ι → A} {x : A}
    (hone : τ 1=1) (ha : Tendsto (fun i => norm τ (a i-x)) l (𝓝 0)) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i => _root_.norm_nonneg _) (fun i => by
    simpa only [map_sub] using norm_trace_le τ hτ hone (a i-x)) ha

end Kadison.TracialL2

end

end
end

end OAI
