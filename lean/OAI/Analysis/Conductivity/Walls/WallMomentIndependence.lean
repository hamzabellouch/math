import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactFiberPrimitive

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory Matrix

lemma deriv_zero_on_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hz : ∀ x∈U, f x=0) {x : ℝ} (hx : x∈U) : deriv f x=0 := by
  have he : f =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hx) hz
  rw [he.deriv_eq,deriv_const]

lemma exp_affine_independent {l r lam A B C : ℝ} (hlr : l<r) (hlam : lam≠0)
    (h : ∀ x∈Ioo l r, A*Real.exp (lam*x)+B+C*x=0) : A=0 ∧ B=0 ∧ C=0 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => A*Real.exp (lam*x)+B+C*x)
      (A*lam*Real.exp (lam*x)+C) x := by
    convert! ((((hasDerivAt_id x).const_mul lam).exp.const_mul A).add
      (hasDerivAt_const x B)).add ((hasDerivAt_id x).const_mul C) using 1
    first | rfl | (simp only [id_eq]; ring)
  have h₁ : ∀ x∈Ioo l r, A*lam*Real.exp (lam*x)+C=0 := by
    intro x hx
    rw [←(hd x).deriv]
    exact deriv_zero_on_open isOpen_Ioo h hx
  have hd₁ (x : ℝ) : HasDerivAt (fun x : ℝ => A*lam*Real.exp (lam*x)+C)
      (A*lam^2*Real.exp (lam*x)) x := by
    convert! (((hasDerivAt_id x).const_mul lam).exp.const_mul (A*lam)).add
      (hasDerivAt_const x C) using 1
    first | rfl | (simp only [id_eq]; ring)
  have h₂ : ∀ x∈Ioo l r, A*lam^2*Real.exp (lam*x)=0 := by
    intro x hx
    rw [←(hd₁ x).deriv]
    exact deriv_zero_on_open isOpen_Ioo h₁ hx
  let x := (l+r)/2
  have hx : x∈Ioo l r := ⟨by dsimp [x]; linarith,by dsimp [x]; linarith⟩
  have hA : A=0 := (mul_eq_zero.mp ((mul_eq_zero.mp (h₂ x hx)).resolve_right
      (Real.exp_ne_zero _))).resolve_right (pow_ne_zero _ hlam)
  have hC : C=0 := by simpa only [hA,zero_mul,zero_add] using h₁ x hx
  exact ⟨hA,by simpa only [hA,hC,zero_mul,zero_add,add_zero] using h x hx,hC⟩

def wallMomentBasis (σ lam s : ℝ) : Fin 3 → ℝ :=
  ![1,-σ*lam*Real.exp (-lam*s),σ*(1+lam*s)*Real.exp (-lam*s)]

lemma wallMomentBasis_smooth (σ lam : ℝ) (i : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => wallMomentBasis σ lam s i) := by
  fin_cases i <;> dsimp [wallMomentBasis] <;> fun_prop

lemma wallMomentBasis_dot (σ lam s : ℝ) (a : Fin 3 → ℝ) :
    a ⬝ᵥ wallMomentBasis σ lam s =
      a 0+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*Real.exp (-lam*s) := by
  simp [wallMomentBasis,dotProduct,Fin.sum_univ_succ]

  ring

lemma wallMomentBasis_independent {l r σ lam : ℝ} (hlr : l<r) (hσ : σ≠0) (hlam : lam≠0)
    (a : Fin 3 → ℝ) (ha : ∀ s∈Ioo l r, a ⬝ᵥ wallMomentBasis σ lam s=0) : a=0 := by
  have he : ∀ s∈Ioo l r,
      a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2)+(σ*lam*a 2)*s=0 := by
    intro s hs
    have h := congrArg (fun t => t*Real.exp (lam*s)) (ha s hs)
    rw [wallMomentBasis_dot] at h
    have hexp : Real.exp (-lam*s)*Real.exp (lam*s)=1 := by
      rw [←Real.exp_add]; simp
    calc
      a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2)+(σ*lam*a 2)*s =
          (a 0+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*Real.exp (-lam*s))*Real.exp (lam*s) := by
        calc
          _ = a 0*Real.exp (lam*s)+(-σ*lam*a 1+σ*a 2+σ*lam*a 2*s)*
              (Real.exp (-lam*s)*Real.exp (lam*s)) := by rw [hexp]; ring
          _ = _ := by ring
      _=0 := by simpa only [zero_mul] using h
  obtain ⟨h₀,h₁,h₂⟩ := exp_affine_independent hlr hlam he
  have ha₂ : a 2=0 := (mul_eq_zero.mp h₂).resolve_left (mul_ne_zero hσ hlam)
  have ha₁ : a 1=0 := by
    have hz : (-σ*lam)*(a 1)=0 := by simpa only [ha₂,mul_zero,add_zero] using h₁
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (neg_ne_zero.mpr hσ) hlam)
  ext i
  fin_cases i <;> assumption

end

open Set MeasureTheory Matrix Topology

lemma positive_interval_bump {l r : ℝ} (_ : l<r) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ s, 0≤χ s) ∧ (∀ s∈Ioo l r, 0<χ s) ∧ tsupport χ ⊆ Icc l r := by
  obtain ⟨χ,hχ,hc,hb⟩ := (isOpen_Ioo : IsOpen (Ioo l r)).exists_contDiff_support_eq (n := ⊤)
  have hs : tsupport χ⊆Icc l r := by
    change closure (Function.support χ) ⊆ Icc l r
    rw [hχ]
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  refine ⟨χ,hc,isCompact_Icc.of_isClosed_subset isClosed_closure hs,
    fun s => (hb ⟨s,rfl⟩).1,?_,hs⟩
  intro s hs'
  have hn : χ s≠0 := by simpa only [←hχ,Function.mem_support] using hs'
  exact (hb ⟨s,rfl⟩).1.lt_of_ne' hn

theorem wall_moment_right_inverse {l r σ lam : ℝ} (hlr : l<r)
    (hσ : σ≠0) (hlam : lam≠0) (b : Fin 3 → ℝ) :
    ∃ a : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) a ∧ HasCompactSupport a ∧
      tsupport a ⊆ Icc l r ∧
      (∀ i, (∫ s, a s*wallMomentBasis σ lam s i)=b i) := by
  obtain ⟨χ,hc,hs,hn,hp,hsub⟩ := positive_interval_bump hlr
  have hG := compactMomentGram_posDef hc.continuous hs
    (fun i => (wallMomentBasis_smooth σ lam i).continuous) hn hp
    (wallMomentBasis_independent hlr hσ hlam)
  obtain ⟨a,ha,has,hasub,ham⟩ := compactMoment_surjective hc hs
    (wallMomentBasis_smooth σ lam) hG b
  exact ⟨a,ha,has,hasub.trans hsub,ham⟩

end ScalarConductivity

end

end OAI
