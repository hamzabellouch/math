import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves
import OAI.Analysis.Conductivity.Branching.CascadeProfile

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma compact_iteratedFDeriv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((hfc.iteratedFDeriv n).isCompact_range
    (((contDiff_infty.mp hf) n).continuous_iteratedFDeriv le_rfl)).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
  exact (hC _ (mem_range_self x)).trans (le_max_left _ _)

lemma sin_cos_iterated_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n sin x‖ ≤ 1 ∧ ‖iteratedDeriv n cos x‖ ≤ 1 := by
  induction n with
  | zero => simpa using And.intro (abs_sin_le_one x) (abs_cos_le_one x)
  | succ n ih => simpa only [iteratedDeriv_add_one_sin,iteratedDeriv_add_one_cos,
      Pi.neg_apply,norm_neg] using ih.symm

lemma linear_comp_iterated_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} (g : F →L[ℝ] E)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {order : ℕ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ order f x‖ ≤ C)
    (x : F) : ‖iteratedFDeriv ℝ order (f ∘ g) x‖ ≤ C*‖g‖^order := by
  rw [g.iteratedFDeriv_comp_right ((contDiff_infty.mp hf) order) x le_rfl]
  exact ((iteratedFDeriv ℝ order f (g x)).norm_compContinuousLinearMap_le (fun _ => g)).trans
    (by simpa using mul_le_mul_of_nonneg_right (hC (g x)) (by positivity : 0≤‖g‖^order))

def cascadeMother (L K : ℝ) (axis : Fin 3) (x : Coord3) : ℝ :=
  cascadeProfile L K (x 0)*cos (x axis)

lemma cascadeMother_smooth (L K : ℝ) (axis : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cascadeMother L K axis) := by
  exact ((cascadeProfile_smooth L K).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff).mul
    (Real.contDiff_cos.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) axis).contDiff)

lemma cascadeMother_iterated_bound {L K : ℝ} (hL : 0 < L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (axis : Fin 3) (x : Coord3),
      ‖iteratedFDeriv ℝ n (cascadeMother L K axis) x‖ ≤ C := by
  have hp : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ i (cascadeProfile L K) x‖ ≤ C :=
    compact_iteratedFDeriv_bound (cascadeProfile_smooth L K) (cascadeProfile_compact hL)
  choose C hC0 hC using hp
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  let b : Fin 3 → ℝ := fun axis => ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ)*(C i*‖P 0‖^i)*(1*‖P axis‖^(n-i))
  refine ⟨∑ axis, b axis,Finset.sum_nonneg (fun a _ => ?_),fun axis x => ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity))) (by positivity))
  · apply le_trans (norm_iteratedFDeriv_mul_le
      ((cascadeProfile_smooth L K).comp (P 0).contDiff)
      (Real.contDiff_cos.comp (P axis).contDiff) x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    apply le_trans (b := b axis)
    · apply Finset.sum_le_sum
      intro i hi
      have h₁ := linear_comp_iterated_bound (P 0) (cascadeProfile_smooth L K) (hC i) x
      have h₂ := linear_comp_iterated_bound (P axis) Real.contDiff_cos
        (fun z => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
          (sin_cos_iterated_bound (n-i) z).2) x
      exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity)))
    · change b axis ≤ ∑ a, b a
      apply Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity))) (by positivity)))
        (Finset.mem_univ axis)

lemma scaled_iterated_bound {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {order : ℕ} {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ order f x‖ ≤ C) (a p : ℝ) (b x : Coord3) :
    ‖iteratedFDeriv ℝ order (fun y => a*f (p • (y-b))) x‖ ≤ |a| * C * |p|^order := by
  let g : Coord3 →L[ℝ] Coord3 := p • ContinuousLinearMap.id ℝ Coord3
  have he : (fun y => a*f (p • (y-b))) = a • (fun y => (f ∘ g) (y-b)) := by rfl
  have hfb : ContDiff ℝ order (fun y => (f ∘ g) (y-b)) :=
    ((contDiff_infty.mp hf) order).comp (g.contDiff.comp (contDiff_id.sub contDiff_const))
  rw [he,iteratedFDeriv_const_smul_apply hfb.contDiffAt,norm_smul,iteratedFDeriv_comp_sub]
  have hh := linear_comp_iterated_bound g hf hC (x-b)
  have hg : ‖g‖ = |p| := by simp [g,norm_smul,ContinuousLinearMap.norm_id,Real.norm_eq_abs]
  rw [hg] at hh
  simpa only [Real.norm_eq_abs,mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg a)

theorem geometric_scaled_C2 {f : ℕ → Coord3 → ℝ}
    (hf : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ C)
    {q : ℝ} (hq : 0 ≤ q) (hqsmall : 4*q<1) (A k : ℝ) (center : ℕ → Coord3) :
    ContDiff ℝ 2 (fun x => ∑' j : ℕ, (A*q^j)*f j ((k*2^j) • (x-center j))) := by
  choose C hC0 hC using hb
  let v : ℕ → ℕ → ℝ := fun n j => |A| * C n * |k|^n*(q*(2:ℝ)^n)^j
  apply contDiff_tsum (v := v)
  · intro j
    exact contDiff_const.mul (((contDiff_infty.mp (hf j)) 2).comp
      ((contDiff_id.sub contDiff_const).const_smul (k*2^j)))
  · intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    have hc : ‖q*(2:ℝ)^n‖ < 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hp : (2:ℝ)^n ≤ 4 := by
        calc (2:ℝ)^n ≤ 2^2 := pow_le_pow_right₀ (by norm_num) hn'
             _ = 4 := by norm_num
      nlinarith
    exact (summable_geometric_of_norm_lt_one hc).mul_left _
  · intro n j x hn
    have hh := scaled_iterated_bound (hf j) (hC n j) (A*q^j) (k*2^j) (center j) x
    apply hh.trans_eq
    dsimp [v]
    rw [abs_mul,abs_pow,abs_of_nonneg hq,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2),
      mul_pow,mul_pow,←pow_mul,←pow_mul]
    ring

def BoundedSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C

lemma BoundedSmooth.of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f) : BoundedSmooth f :=
  ⟨hf,compact_iteratedFDeriv_bound hf hc⟩

lemma BoundedSmooth.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  obtain ⟨D,hD,hDg⟩ := hg.2 n
  refine ⟨C+D,add_nonneg hC hD,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ C+D
  rw [iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt
    (hg.1.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCf x) (hDg x))

lemma BoundedSmooth.smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BoundedSmooth f) (a : ℝ) : BoundedSmooth (fun x => a*f x) := by
  refine ⟨contDiff_const.mul hf.1,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  refine ⟨|a| * C,mul_nonneg (abs_nonneg _) hC,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (a • f) x‖ ≤ |a| * C
  rw [iteratedFDeriv_const_smul_apply ((contDiff_infty.mp hf.1) n).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hCf x) (abs_nonneg _)

lemma BoundedSmooth.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma BoundedSmooth.mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x*g x) := by
  choose C hC hCf using hf.2
  choose D hD hDg using hg.2
  refine ⟨hf.1.mul hg.1,fun n => ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*C i*D (n-i),?_,?_⟩⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hD _)
  · intro x
    apply (norm_iteratedFDeriv_mul_le hf.1 hg.1 x
      (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).trans
    exact Finset.sum_le_sum fun i _ => mul_le_mul
      (mul_le_mul_of_nonneg_left (hCf i x) (Nat.cast_nonneg _)) (hDg (n-i) x)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))

lemma BoundedSmooth.comp_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} (hf : BoundedSmooth f)
    (g : F →L[ℝ] E) : BoundedSmooth (f ∘ g) := by
  refine ⟨hf.1.comp g.contDiff,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  exact ⟨C*‖g‖^n,mul_nonneg hC (by positivity),linear_comp_iterated_bound g hf.1 hCf⟩

lemma BoundedSmooth.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BoundedSmooth f) (b : E) : BoundedSmooth (fun x => f (x-b)) := by
  refine ⟨hf.1.comp (contDiff_id.sub contDiff_const),fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  refine ⟨C,hC,fun x => ?_⟩
  rw [iteratedFDeriv_comp_sub]
  exact hCf (x-b)

lemma sin_boundedSmooth : BoundedSmooth Real.sin :=
  ⟨Real.contDiff_sin,fun n => ⟨1,by norm_num,fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using (sin_cos_iterated_bound n x).1⟩⟩
lemma cos_boundedSmooth : BoundedSmooth Real.cos :=
  ⟨Real.contDiff_cos,fun n => ⟨1,by norm_num,fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using (sin_cos_iterated_bound n x).2⟩⟩

end ScalarConductivity

end

end OAI
