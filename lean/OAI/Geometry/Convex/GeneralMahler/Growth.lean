import Mathlib

namespace OAI
/-! Elementary bounds used throughout the Gaussian and layer integrations.
We keep pointwise growth and measurability hypotheses separate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Real
open scoped Topology ENNReal RealInnerProductSpace NNReal
namespace GeneralMahler
section
variable {X Y E F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

def PolyBound (f : X → E) : Prop :=
  ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n

namespace PolyBound

theorem of_bound {f : X → E} (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C) : PolyBound f :=
  ⟨C,0, le_trans (norm_nonneg (f 0)) (h 0), by simpa⟩

theorem const (v : E) : PolyBound (fun _ : X => v) := of_bound _ (fun _ => le_rfl)

theorem id : PolyBound (fun x : X => x) :=
  ⟨1,1,zero_le_one,by simp⟩

theorem clm [NormedSpace ℝ X] [NormedSpace ℝ E] (f : X →L[ℝ] E) :
    PolyBound f :=
  ⟨‖f‖, 1,norm_nonneg _, fun x => (f.le_opNorm x).trans (by
    gcongr; simp)⟩

variable {f g : X → E}
theorem mono {h : X → F} (hf : PolyBound f) (H : ∀ x, ‖h x‖ ≤ ‖f x‖) :
    PolyBound h := by
  obtain ⟨C,n,hc,hb⟩ := hf
  exact ⟨C,n,hc,fun x => (H x).trans (hb x)⟩

lemma raise_le (C b : ℝ) (hc : 0 ≤ C) (hb : 1 ≤ b) (n m : ℕ) :
    C*b^n ≤ C*b^(n+m) := by gcongr; omega
lemma common {h : X → F} (hf : PolyBound f) (hg : PolyBound h) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n ∧ ‖h x‖ ≤ C*(1+‖x‖)^n := by
  obtain ⟨C,n,hc,hn⟩ := hf
  obtain ⟨D,m,hd,hm⟩ := hg
  refine ⟨C+D, n+m, by positivity, fun x => ?_⟩
  constructor
  · apply le_trans (hn x); gcongr <;> simp_all
  · apply le_trans (hm x); gcongr <;> simp_all

theorem add (hf : PolyBound f) (hg : PolyBound g) : PolyBound fun x => f x + g x := by
  obtain ⟨C,n,hc,hb⟩ := common hf hg
  refine ⟨2*C,n,by positivity, fun x => (norm_add_le ..).trans ?_⟩
  obtain ⟨h,h'⟩ := hb x; linarith
theorem neg (hf : PolyBound f) : PolyBound fun x => -f x := hf.mono (by simp)
theorem sub (hf : PolyBound f) (hg : PolyBound g) : PolyBound fun x => f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
theorem norm (hf : PolyBound f) : PolyBound fun x => ‖f x‖ :=
  hf.mono (fun _ => (Real.norm_of_nonneg (norm_nonneg _)).le)
lemma of_prod_le {K : Type*} [SeminormedAddCommGroup K] {h : X → F}
    {l : X → K} (hf : PolyBound f) (hh : PolyBound h) (hl : ∀ x, ‖l x‖ ≤ ‖f x‖*‖h x‖) :
    PolyBound l := by
  obtain ⟨C,n,hc,hn⟩ := common hf hh
  refine ⟨C*C,n+n,by positivity,fun x => (hl x).trans ?_⟩
  obtain ⟨h₁,h₂⟩ := hn x
  calc
    _ ≤ (C*(1+‖x‖)^n)*(C*(1+‖x‖)^n) := mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring
theorem smul [NormedSpace ℝ E] {a : X → ℝ} (ha : PolyBound a) (hf : PolyBound f) :
    PolyBound fun x => a x • f x :=
  of_prod_le ha hf (fun _x => (norm_smul _ _).le)
theorem mul {R : Type*} [NormedRing R] {b d : X → R} (hb : PolyBound b) (hd : PolyBound d) :
    PolyBound fun x => b x * d x :=
  of_prod_le hb hd fun _ => norm_mul_le _ _
theorem pow {R : Type*} [NormedRing R] {b : X → R} (hb : PolyBound b) (n : ℕ) :
    PolyBound fun x => b x ^ n := by
  induction n with
  | zero => simpa using (const (X := X) (1 : R))
  | succ n ih => simpa [pow_succ] using ih.mul hb
theorem prodMk {h : X → F} (hf : PolyBound f) (hh : PolyBound h) :
    PolyBound fun x => (f x,h x) := by
  obtain ⟨C,n,hc,hb⟩ := common hf hh
  exact ⟨C,n,hc,fun x => max_le (hb x).1 (hb x).2⟩
theorem fst : PolyBound (Prod.fst (α := X) (β := E)) := id.mono fun _x => le_max_left ..
theorem snd : PolyBound (Prod.snd (α := X) (β := E)) := id.mono fun _x => le_max_right ..
theorem comp {b : E → F} (hb : PolyBound b) (hf : PolyBound f) :
    PolyBound fun x => b (f x) := by
  obtain ⟨C,n,hc,h⟩ := hb
  obtain ⟨D,m,hd,h'⟩ := hf
  refine ⟨C*(1+D)^n, m*n, by positivity, fun x => (h _).trans ?_⟩
  calc
    _ ≤ C*((1+D)*(1+‖x‖)^m)^n := by
      have hv : (1:ℝ) ≤ (1+‖x‖)^m := one_le_pow₀ (by simp)
      gcongr; linarith [h' x]
    _ = _ := by rw [mul_pow,pow_mul,mul_assoc]

theorem linear_growth {K : ℝ≥0} (h : LipschitzWith K f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖) := by
  refine ⟨K+‖f 0‖,by positivity, fun x => ?_⟩
  have hi : ‖f x - f 0‖ ≤ K*‖x‖ := by simpa [dist_eq_norm] using h.dist_le_mul x 0
  have hh := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at hh
  nlinarith [norm_nonneg (f 0),norm_nonneg x]

theorem lipschitz {K : ℝ≥0} (hf : LipschitzWith K f) : PolyBound f := by
  obtain ⟨C,hc,h⟩ := linear_growth hf
  exact ⟨C,1,hc,by simpa using h⟩

theorem indicator (s : Set X) (hf : PolyBound f) :
    PolyBound (s.indicator f) := hf.mono (fun x => by
  classical
  by_cases hx : x ∈ s <;> simp [hx])
end PolyBound
end

section Integrability
open ProbabilityTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  {μ : Measure E} [IsGaussian μ]

lemma integrable_envelope (n : ℕ) :
    Integrable (fun x:E => (1+‖x‖)^n) μ := by
  cases n with
  | zero => simp
  | succ n =>
    let p : ℝ≥0∞ := ↑(n+1 : ℕ)
    have hI := IsGaussian.memLp_id μ p (by simp [p])
    have hW : MemLp (fun _ : E => (1:ℝ)) p μ := memLp_const _
    have hf : MemLp (fun x:E => (1+‖x‖)) (↑(n+1 : ℕ)) μ := hW.add hI.norm
    have he := hf.integrable_norm_rpow (by simp) (by simp)
    have hnorm (x:E) : ‖1+‖x‖‖ = 1+‖x‖ := Real.norm_of_nonneg (by positivity)
    simpa only [hnorm, ENNReal.toReal_natCast, Real.rpow_natCast] using he

theorem PolyBound.gaussian_integrable {f : E → F}
    (h : PolyBound f) (hm : AEStronglyMeasurable f μ) : Integrable f μ := by
  obtain ⟨C,n,hc,he⟩ := h
  exact ((integrable_envelope n).const_mul C).mono' hm (ae_of_all _ he)
end Integrability
end GeneralMahler

end

end OAI
