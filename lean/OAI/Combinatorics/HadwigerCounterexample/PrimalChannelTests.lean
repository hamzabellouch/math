import OAI.Combinatorics.HadwigerCounterexample.GramCharacterQuotients

namespace OAI

/-! # Primal Channel Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

private theorem cp_rep (f : Module.Dual F (Cross p n)) :
    ∃ M : Cross p n,cpDual p M=f := by
  classical
  let B : Cross p n →ₗ[F] Module.Dual F (Cross p n) := {
    toFun := cpDual p
    map_add' := by
      intro x y
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.add_apply]
      simp only [cpDual_val,Pi.add_apply,mpair_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.smul_apply]
      simp only [cpDual_val,Pi.smul_apply,mpair_smul,RingHom.id_apply,smul_eq_mul,Finset.mul_sum] }
  have hb : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot]
    refine le_bot_iff.mp (fun x hx => ?_)
    have h1 : x = 0 := by
      funext i
      apply mpair_nondeg
      refine LinearMap.ext fun y => ?_
      change cpDual p x=0 at hx
      have h := LinearMap.congr_fun hx (Pi.single i y)
      rw [cpDual_val,Finset.sum_eq_single i] at h
      · rwa [Pi.single_eq_same] at h
      · intro j _ hj; simp [hj]
      simp
    rw [h1]; exact Submodule.zero_mem _
  exact rk_surj.mpr ((rk_inj.mp hb).trans Subspace.dual_finrank_eq.symm) f

abbrev CheckOne (p : Shape) (n : ℕ) :=
  Place p → Bool → Bool → Mat (Chan p) (Row p n)
abbrev CheckGram (p : Shape) (n : ℕ) :=
  CheckOne p n × CheckOne p n
instance cgOneFin (p : Shape) (n : ℕ) : Fintype (CheckOne p n) := by
  classical
  letI : Fintype (Mat (Chan p) (Row p n)) := inferInstance
  letI : Fintype (Bool → Bool → Mat (Chan p) (Row p n)) := inferInstance
  exact inferInstance
instance cgFin (p : Shape) (n : ℕ) : Fintype (CheckGram p n) := inferInstance

def testgram (p : Shape) {n} : Cross p n →ₗ[F] CheckGram p n where
  toFun A := (scalarBlocks p A, scalarBlocks p (reciprocal p A))
  map_add' A B := by
    apply Prod.ext <;>
    · ext; simp only [Pi.add_apply,Prod.fst_add,Prod.snd_add,
        scalarBlocks,channelOut,reciprocal,Matrix.add_apply,Matrix.add_mul,Matrix.transpose_add]
  map_smul' a A := by
    apply Prod.ext <;>
    · ext; simp only [Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
        scalarBlocks,channelOut,reciprocal,Matrix.smul_apply,Matrix.smul_mul,Matrix.transpose_smul,
        RingHom.id_apply]

theorem checkgram_dim :
    dim (CheckGram p n)=16*ncComp p*p.h*Fintype.card (Row p n) := by
  classical
  let r := p.h*Fintype.card (Row p n)
  let T := Mat (Chan p) (Row p n)
  have hf : finrank F T=r := (dim_mat _ _).trans (by simp [r,Chan])
  have hg {I V : Type} [Fintype I] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
      finrank F (I→V) = Fintype.card I * finrank F V := by
    rw [finrank_pi_fintype]; simp
  have h : finrank F (CheckOne p n)=8*ncComp p*r := by
    unfold CheckOne
    rw [hg,hg,hg,hf]
    simp [ncComp,Place]
    ring
  unfold CheckGram dim
  rw [Module.finrank_prod,h]
  unfold r; ring

theorem indicator_test {V A : Type} [Fintype A] [AddCommGroup V] [Module F V]
    [Fintype V] (s : A → V) (w : Wgt A) (hw : IsLaw w) (ε : ℝ) (he : 0≤ε)
    (hc : ∀ f : Module.Dual F V, let Y := avg w (fun x => wsign (f (s x))); Y=1 ∨ |Y|≤ε) :
    bp (-(dim V:ℝ))- ε ≤ pr w (fun x => s x=0) := by
  classical
  let T := Module.Dual F V
  have : Finite T := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype T := Fintype.ofFinite T
  have h (v : V) : ind (v=0) = avg unif (fun f : T => wsign (f v)) := by
    have h := wsign_lin (Module.evalEquiv F V v)
    rw [map_eq_zero_iff _ (Module.evalEquiv F V).injective] at h
    exact h.symm
  unfold pr
  simp_rw [h]
  rw [avg_avg]
  let E (v : T) := ind (v=0)
  have hE : avg unif E = bp (-(dim V:ℝ)) := by
    change pr unif (fun v : T => v=0)=_
    rw [pr_point',unif_apply,card_space,
      show dim T=dim V from Subspace.dual_finrank_eq,bp_neg]
  rw [← hE,show avg unif E - ε= avg unif (fun v : T => E v-ε) from (by
    rw [avg_sub,unif_law.avg_const])]
  refine avg_mono unif_law.nz fun x => ?_
  by_cases hh : x=0
  · subst x
    change ind (0= (0:T))-ε ≤ avg w (fun _ => wsign 0)
    rw [ind_one rfl,hw.avg_const,wsign_zero]; linarith
  unfold E
  rw [ind_zero hh,zero_sub]
  rcases hc x with hi|hi
  · rw [hi]; linarith
  exact (abs_le.mp hi).1

theorem gram_hit (Q : Cross p n) {u w : Wgt (UnitType p n N)}
    (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (h : ∀ x,u x≠0 → ∀ y,w y≠0 → rowAgree f.sp (actual p x y) Q ∧
      rowAgree b.sp (actual p y x) (reciprocal p Q))
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ)≤0.01*N) :
    hit N ≤ pr (pairW u w) (fun x =>
      testgram p (actual p x.1 x.2)=testgram p Q) := by
  classical
  let v := pairW u w
  let s (x : UnitType p n N × UnitType p n N) := testgram p (actual p x.1 x.2 - Q)
  have hh (g : Module.Dual F (CheckGram p n)) :
      let Y := avg v (fun x => wsign (g (s x)))
      Y=1 ∨ |Y|≤bp (-0.45*N) := by
    obtain ⟨M,hM⟩ := cp_rep (g ∘ₗ testgram p)
    have hf x := LinearMap.congr_fun hM x
    have he x : g (s x) = cpDual p M _ := (hf (actual p x.1 x.2-Q)).symm
    dsimp only
    simp_rw [he]
    exact gramCharacter Q M hu hw hc hd h
  have hg := indicator_test s v (pairW_law hu hw) (bp (-0.45*N)) (bp_pos _).le hh
  have he : pr v (fun x => s x=0)=pr v (fun x => testgram p (actual p x.1 x.2)=testgram p Q) := by
    apply congrArg (pr v)
    funext x; apply propext
    unfold s
    have he (A : Cross p n) : testgram p (A+Q) = testgram p A+testgram p Q := (testgram p).map_add' _ _
    rw [show actual p x.1 x.2-Q=actual p x.1 x.2+Q from ZModModule.sub_eq_add ..,he, ← ZModModule.sub_eq_add,sub_eq_zero]
  rw [he] at hg
  refine le_trans ?_ hg
  have hn : 100≤(N:ℝ) := by exact_mod_cast hN
  unfold hit
  have heq := bp_le (show -0.45*N≤-0.02*(N:ℝ) by linarith only [hn])
  have heq' : 2*bp (-0.02*N) ≤ bp (-(dim (CheckGram p n):ℝ)) := by
    rw [← bp_one,← bp_add]; apply bp_le; linarith only [hn,hT]
  linarith only [heq,heq']

end HadwigerCounterexample

end

end OAI
