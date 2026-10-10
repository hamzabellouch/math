import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open scoped Classical
open Set Filter
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma pdist_nonneg (p q : V × ℝ) : 0≤pdist p q := by unfold pdist; positivity
omit [NormedSpace ℝ E] in
lemma HolderBound.mono {α K L : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (h : HolderBound α Ω f K) (hKL : K≤L) : HolderBound α Ω f L :=
  ⟨fun p hp => (h.1 p hp).trans hKL,fun p hp q hq => (h.2 p hp q hq).trans
    (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg (pdist_nonneg p q) _))⟩
omit [NormedSpace ℝ E] in
lemma HolderBound.restrict {α K : ℝ} {Ω Ω' : Set (V × ℝ)} {f : V × ℝ → E}
    (h : HolderBound α Ω f K) (hs : Ω'⊆Ω) : HolderBound α Ω' f K :=
  ⟨fun p hp => h.1 p (hs hp),fun p hp q hq => h.2 p (hs hp) q (hs hq)⟩
omit [NormedSpace ℝ E] in
lemma HolderBound.add {α K L : ℝ} {Ω : Set (V × ℝ)} {f g : V × ℝ → E}
    (hf : HolderBound α Ω f K) (hg : HolderBound α Ω g L) :
    HolderBound α Ω (fun p => f p+g p) (K+L) := by
  refine ⟨fun p hp => (norm_add_le _ _).trans (add_le_add (hf.1 p hp) (hg.1 p hp)),?_⟩
  intro p hp q hq
  rw [show (f p+g p)-(f q+g q)=(f p-f q)+(g p-g q) by abel]
  exact (norm_add_le _ _).trans ((add_le_add (hf.2 p hp q hq) (hg.2 p hp q hq)).trans_eq (by ring))
lemma HolderBound.clm {α K : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (h : HolderBound α Ω f K) (L : E →L[ℝ] F) :
    HolderBound α Ω (fun p => L (f p)) (‖L‖*K) := by
  refine ⟨fun p hp => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.1 p hp) (norm_nonneg _)),?_⟩
  intro p hp q hq
  rw [←map_sub]
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.2 p hp q hq) (norm_nonneg _)).trans_eq (by ring))
lemma HolderBound.smul {α A B : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → ℝ} {g : V × ℝ → E}
    (hf : HolderBound α Ω f A) (hg : HolderBound α Ω g B) (hA : 0≤A) (hB : 0≤B) :
    HolderBound α Ω (fun p => f p • g p) (2*A*B) := by
  refine ⟨?_,?_⟩
  · intro p hp
    rw [norm_smul]
    exact (mul_le_mul (hf.1 p hp) (hg.1 p hp) (norm_nonneg _) hA).trans (by nlinarith [mul_nonneg hA hB])
  · intro p hp q hq
    rw [show f p • g p-f q • g q=f p • (g p-g q)+(f p-f q) • g q by rw [smul_sub,sub_smul]; abel]
    apply (norm_add_le _ _).trans
    simp only [norm_smul]
    have h1 := mul_le_mul (hf.1 p hp) (hg.2 p hp q hq) (norm_nonneg _) hA
    have h2 := mul_le_mul (hf.2 p hp q hq) (hg.1 q hq) (norm_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (pdist_nonneg p q) _))
    nlinarith

lemma supported_freezing_error (α ε K M N : ℝ) (Ω S : Set (V × ℝ))
    (a : V × ℝ → ℝ) (g : V × ℝ → E) (hε : 0≤ε) (hK : 0≤K) (hM : 0≤M) (hN : 0≤N)
    (hgs : ∀ p∈Ω, p∉S → g p=0)
    (has : ∀ p∈Ω, p∈S → ‖a p‖≤ε)
    (hah : ∀ p∈Ω, p∈S → ∀ q∈Ω, q∈S → ‖a p-a q‖≤K*pdist p q^α)
    (hg : ∀ p∈Ω, ‖g p‖≤N)
    (hgh : ∀ p∈Ω, ∀ q∈Ω, ‖g p-g q‖≤M*pdist p q^α) :
    HolderBound α Ω (fun p => if p∈S then a p • g p else 0) (ε*M+K*N+ε*N) := by
  classical
  have hNε : 0≤ε*N := mul_nonneg hε hN
  have hKN : 0≤K*N := mul_nonneg hK hN
  have hεM : 0≤ε*M := mul_nonneg hε hM
  refine ⟨?_,?_⟩
  · intro p hp
    change ‖(if p∈S then a p • g p else 0)‖≤_
    split_ifs with hs
    · rw [norm_smul]
      exact (mul_le_mul (has p hp hs) (hg p hp) (norm_nonneg _) hε).trans (by linarith)
    · simpa using (show 0≤ε*M+K*N+ε*N by positivity)
  · intro p hp q hq
    change ‖(if p∈S then a p • g p else 0)-(if q∈S then a q • g q else 0)‖≤_
    have hd : 0≤pdist p q^α := Real.rpow_nonneg (pdist_nonneg p q) _
    by_cases hs : p∈S <;> by_cases ht : q∈S
    · simp only [ite_eq_left hs,ite_eq_left ht]
      rw [show a p • g p-a q • g q=a p • (g p-g q)+(a p-a q) • g q by rw [smul_sub,sub_smul]; abel]
      apply (norm_add_le _ _).trans
      simp only [norm_smul]
      have h1 := mul_le_mul (has p hp hs) (hgh p hp q hq) (norm_nonneg _) hε
      have h2 := mul_le_mul (hah p hp hs q hq ht) (hg q hq) (norm_nonneg _) (mul_nonneg hK hd)
      nlinarith [mul_nonneg hNε hd]
    · simp only [ite_eq_left hs,ite_eq_right ht,sub_zero,norm_smul]
      have hh := hgh p hp q hq
      rw [hgs q hq ht,sub_zero] at hh
      have := mul_le_mul (has p hp hs) hh (norm_nonneg _) hε
      nlinarith [mul_nonneg hKN hd,mul_nonneg hNε hd]
    · simp only [ite_eq_right hs,ite_eq_left ht,zero_sub,norm_neg,norm_smul]
      have hh := hgh p hp q hq
      rw [hgs p hp hs,zero_sub,norm_neg] at hh
      have := mul_le_mul (has q hq ht) hh (norm_nonneg _) hε
      nlinarith [mul_nonneg hKN hd,mul_nonneg hNε hd]
    · simp only [ite_eq_right hs,ite_eq_right ht,sub_self,norm_zero]
      positivity
end ParabolicInterior

end

end OAI
