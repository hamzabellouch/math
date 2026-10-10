import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianLaw

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma project_nonexpansive (B : Body E) (x y : E) : ‖project B x-project B y‖≤‖x-y‖ := by
  have h₀ := project_variational B x (project B y) (project_mem B y)
  have h₁ := project_variational B y (project B x) (project_mem B x)
  let d := project B x-project B y
  have hid : (project B x-x)-(project B y-y)=d-(x-y) := by dsimp [d]; abel
  have hrev : project B y-project B x = -d := by dsimp [d]; abel
  rw [hrev,inner_neg_right] at h₀
  have hi : inner ℝ (d-(x-y)) d≤0 := by rw [← hid,inner_sub_left]; linarith
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hi
  have hb := real_inner_le_norm (x-y) d
  nlinarith [norm_nonneg d,norm_nonneg (x-y)]

lemma walk_initial_contraction (B : Body E) (x y : E) (w : ℕ → E) (N : ℕ) :
    ‖walk B x w N-walk B y w N‖≤‖x-y‖ := by
  induction N with
  | zero => exact le_rfl
  | succ N hN =>
      rw [walk,walk]
      exact (project_nonexpansive B _ _).trans (by simpa only [add_sub_add_right_eq_sub] using hN)

lemma walk_prefix_eq (B : Body E) (x : E) (w v : ℕ → E) (N : ℕ)
    (h : ∀i≤N,w i=v i) : walk B x w N=walk B x v N := by
  induction N with
  | zero => rfl
  | succ N hN =>
      simp only [walk,hN (fun i hi => h i (hi.trans (Nat.le_succ _))),h N (Nat.le_succ _),h (N+1) le_rfl]

end ConvexSkorokhod

namespace BrownianForcing

open MeasureTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma map_initial_contraction (B : Body E) (x y : E) (Φ Ψ : VectorPath E → VectorPath E)
    (hΦ : IsReflectedMap B x Φ) (hΨ : IsReflectedMap B y Ψ) (f : VectorPath E) :
    ‖Φ f-Ψ f‖≤‖x-y‖ := by
  obtain ⟨u,k,ν,hvalues,hu,hk,hu0,hk0,hbody,hconv,hrest⟩ := hΦ f
  obtain ⟨v,l,ζ,hvaluesv,hv,hl,hv0,hl0,hbodyv,hconvv,hrestv⟩ := hΨ f
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro t
  change ‖Φ f t-Ψ f t‖≤‖x-y‖
  rw [hvalues,hvaluesv]
  apply le_of_tendsto (((hconv.tendsto_at t.2).sub (hconvv.tendsto_at t.2)).norm)
  exact Filter.Eventually.of_forall fun n => walk_initial_contraction B x y _ _

lemma map_causal (B : Body E) (x : E) (Φ : VectorPath E → VectorPath E)
    (hΦ : IsReflectedMap B x Φ) (f g : VectorPath E) (t : Set.Icc (0:ℝ) 1)
    (hfg : ∀s : Set.Icc (0:ℝ) 1,s≤t → f s=g s) : Φ f t=Φ g t := by
  obtain ⟨u,k,ν,hvalues,hu,hk,hu0,hk0,hbody,hconv,hrest⟩ := hΦ f
  obtain ⟨v,l,ζ,hvaluesv,hv,hl,hv0,hl0,hbodyv,hconvv,hrestv⟩ := hΦ g
  rw [hvalues,hvaluesv]
  have hmesh (n : ℕ) : mesh B x (extendPath f) (n+1) t=mesh B x (extendPath g) (n+1) t := by
    apply walk_prefix_eq
    intro i hi
    have hN : (0:ℝ)<(n+1:ℕ) := by positivity
    have hit : (i:ℝ)/(n+1:ℕ)≤(t:ℝ) := by
      apply (div_le_iff₀ hN).mpr
      exact (Nat.cast_le.mpr hi).trans (Nat.floor_le (mul_nonneg t.2.1 hN.le))
    have hs : (i:ℝ)/(n+1:ℕ)∈Icc (0:ℝ) 1 := ⟨by positivity,hit.trans t.2.2⟩
    change extendPath f ((i:ℝ)/(n+1:ℕ))=extendPath g ((i:ℝ)/(n+1:ℕ))
    rw [show (i:ℝ)/(n+1:ℕ)=(⟨(i:ℝ)/(n+1:ℕ),hs⟩ : Set.Icc (0:ℝ) 1) by rfl]
    rw [extendPath_apply,extendPath_apply]
    exact hfg _ hit
  exact tendsto_nhds_unique (hconv.tendsto_at t.2) ((hconvv.tendsto_at t.2).congr (fun n => (hmesh n).symm))

end BrownianForcing

end OAI
