import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ComplexGramTrace
import OAI.Geometry.SmoothYau.Estimates.DirectionalLinearComp
import OAI.Geometry.SmoothYau.Estimates.ProductSphereFstContraction

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def productSphere_fstPower (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    WithLp 2 (Euclidean n×Euclidean m) → ℂ :=
  (fun y => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k) ∘
    WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_smooth (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_fstPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_zero (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    productSphere_fstPower (n:=n) (m:=m) p ℓ k 0 = (ℓ p)^k := by
  simp [productSphere_fstPower,roundChart_zero]
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_first (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ)
    (v : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (productSphere_fstPower p ℓ k) 0 v =
      (k:ℂ)*(ℓ p)^(k-1)*ℓ (unitSphereFrame (n:=n) p v.fst) := by
  unfold productSphere_fstPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [directional_linear_comp (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k)) (hf.differentiable (by simp))]
  simp only [ContinuousLinearMap.map_zero]
  rw [roundLinearPower_directional]
  simp [roundChart_zero,(roundChart_first _ _).fderiv]
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_second (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ)
    (k : ℕ) (hk : 2 ≤ k) (v w : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (fun y => fderiv ℝ (productSphere_fstPower p ℓ k) y w) 0 v =
      (k:ℂ)*((k:ℂ)-1)*(ℓ p)^(k-2)*ℓ (unitSphereFrame (n:=n) p v.fst)*
        ℓ (unitSphereFrame (n:=n) p w.fst) -
      (k:ℂ)*(ℓ p)^k*(inner ℝ w.fst v.fst:ℂ) := by
  unfold productSphere_fstPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [second_linear_comp (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k)) hf]
  simp only [ContinuousLinearMap.map_zero]
  exact roundLinearPower_second_of_two_le ℓ k hk _ _ _ _
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (a b : A) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    complexGramTrace e (fun v w => fderiv ℝ
      (fun y => fderiv ℝ (productSphere_fstPower p (planarLinear a b) k) y w) 0 v) =
      -(k:ℂ)*((k:ℂ)+(n:ℂ)-1)*(planarLinear a b p)^k := by
  simp_rw [productSphere_fstPower_second p _ k hk]
  have ht : (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
      (inner ℝ (e j).fst (e i).fst:ℂ)) = (n:ℂ) := by
    simp only [← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [lp_inverse_gram_fst_trace]
    simp [Euclidean]
  let z := planarLinear a b (p:A)
  calc
    _ = (k:ℂ)*((k:ℂ)-1)*z^(k-2)*
        (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          planarLinear a b (unitSphereFrame p (e j).fst)*
          planarLinear a b (unitSphereFrame p (e i).fst)) -
        (k:ℂ)*z^k*(∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          (inner ℝ (e j).fst (e i).fst:ℂ)) := by
      unfold complexGramTrace
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [z]
      ring
    _ = _ := by
      rw [productSphere_fst_planar_contraction e p a b ha hb hab,ht]
      have hp : z^(k-2)*z^2=z^k := by rw [← pow_add,Nat.sub_add_cancel hk]
      change (k:ℂ)*((k:ℂ)-1)*z^(k-2)* -(z^2)-(k:ℂ)*z^k*(n:ℂ) = _
      rw [mul_neg,mul_assoc ((k:ℂ)*((k:ℂ)-1)),hp]
      dsimp [z]
      ring

def productSphere_sndPower (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    WithLp 2 (Euclidean n×Euclidean m) → ℂ :=
  (fun y => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) ∘
    WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_zero (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    productSphere_sndPower (n:=n) (m:=m) p ℓ k 0 = (ℓ p)^k := by
  simp [productSphere_sndPower,roundChart_zero]
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_first (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ)
    (v : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (productSphere_sndPower p ℓ k) 0 v =
      (k:ℂ)*(ℓ p)^(k-1)*ℓ (unitSphereFrame (n:=m) p v.snd) := by
  unfold productSphere_sndPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [directional_linear_comp (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k)) (hf.differentiable (by simp))]
  simp only [ContinuousLinearMap.map_zero]
  rw [roundLinearPower_directional]
  simp [roundChart_zero,(roundChart_first _ _).fderiv]
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_second (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ)
    (k : ℕ) (hk : 2 ≤ k) (v w : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (fun y => fderiv ℝ (productSphere_sndPower p ℓ k) y w) 0 v =
      (k:ℂ)*((k:ℂ)-1)*(ℓ p)^(k-2)*ℓ (unitSphereFrame (n:=m) p v.snd)*
        ℓ (unitSphereFrame (n:=m) p w.snd) -
      (k:ℂ)*(ℓ p)^k*(inner ℝ w.snd v.snd:ℂ) := by
  unfold productSphere_sndPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [second_linear_comp (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k)) hf]
  simp only [ContinuousLinearMap.map_zero]
  exact roundLinearPower_second_of_two_le ℓ k hk _ _ _ _
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:B) 1) (a b : B) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    complexGramTrace e (fun v w => fderiv ℝ
      (fun y => fderiv ℝ (productSphere_sndPower p (planarLinear a b) k) y w) 0 v) =
      -(k:ℂ)*((k:ℂ)+(m:ℂ)-1)*(planarLinear a b p)^k := by
  simp_rw [productSphere_sndPower_second p _ k hk]
  have ht : (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
      (inner ℝ (e j).snd (e i).snd:ℂ)) = (m:ℂ) := by
    simp only [← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [lp_inverse_gram_snd_trace]
    simp [Euclidean]
  let z := planarLinear a b (p:B)
  calc
    _ = (k:ℂ)*((k:ℂ)-1)*z^(k-2)*
        (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          planarLinear a b (unitSphereFrame p (e j).snd)*
          planarLinear a b (unitSphereFrame p (e i).snd)) -
        (k:ℂ)*z^k*(∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          (inner ℝ (e j).snd (e i).snd:ℂ)) := by
      unfold complexGramTrace
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [z]
      ring
    _ = _ := by
      rw [productSphere_snd_planar_contraction e p a b ha hb hab,ht]
      have hp : z^(k-2)*z^2=z^k := by rw [← pow_add,Nat.sub_add_cancel hk]
      change (k:ℂ)*((k:ℂ)-1)*z^(k-2)* -(z^2)-(k:ℂ)*z^k*(m:ℂ) = _
      rw [mul_neg,mul_assoc ((k:ℂ)*((k:ℂ)-1)),hp]
      dsimp [z]
      ring
end YauCounterexamples
end

end OAI
