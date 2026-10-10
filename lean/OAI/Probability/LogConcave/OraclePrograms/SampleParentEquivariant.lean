import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TerminalMeanProgram

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

lemma sampleParent_equivariant (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (r T η : ℝ) (Δ : Point d)
    (hE : E.compile.Equivariant
      (moveSeed (fun z => (z.1+r • Δ,z.2-T • Δ)) v Δ) (fun y => y-Δ)) :
    (sampleParent E v T η).pre.Equivariant
      (moveSeed (fun x => x+r • Δ) (sampleParent E v T η).shift Δ) (fun y => y-Δ) := by
  dsimp only [sampleParent]
  apply hE.seedMap _ (by fun_prop) _
  intro z
  apply Prod.ext
  · simp [moveSeed,shiftSlots,Fin.append_left,sub_eq_add_neg]
  · funext i
    simp [moveSeed,shiftSlots,Fin.append_right]

lemma meanParent_equivariant (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) {r T : ℝ} (hT : T≠0) (Δ : Point d)
    (hS : S.program.Equivariant (moveSeed (fun x => x+r • Δ) u Δ)
      (fun y => y-(T⁻¹)^2 • Δ))
    (hE : E.compile.Equivariant
      (moveSeed (fun z => (z.1+r • Δ,(z.2.1-T⁻¹ • Δ,z.2.2))) v Δ) id) :
    (meanParent S E u v T).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (meanParent S E u v T).shift Δ) id := by
  dsimp only [meanParent]
  apply Program.Equivariant.seq (hS.seedMap _ (by unfold leftBlock; fun_prop) _ ?_)
  · apply hE.seedMap _ (by unfold middleBlock rightBlock; fun_prop) _
    intro z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · simp only [moveSeed,smul_sub,smul_smul]
          congr 1
          congr 1
          field_simp
        · simp [moveSeed,shiftSlots,middleBlock]
    · funext i
      simp [moveSeed,shiftSlots,rightBlock]
  · intro z
    apply Prod.ext
    · rfl
    · funext i
      simp [moveSeed,shiftSlots,leftBlock]

lemma sampleParent_lipschitz (V : Point d → ℝ) (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η K : ℝ)
    (hE : ∀x y z g,‖E.eval V (x,z) g-E.eval V (y,z) g‖≤K*‖x-y‖) :
    ∀x y g,‖(sampleParent E v T η).pre.run V (x,g)-(sampleParent E v T η).pre.run V (y,g)‖≤K*‖x-y‖ := by
  intro x y g
  rw [sampleParent_run E v T η V x g,sampleParent_run E v T η V y g]
  exact hE _ _ _ _

lemma meanParent_lipschitz (V : Point d → ℝ) (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T Ks Kx Ky : ℝ)
    (hKy : 0≤Ky) (hT : 0≤T)
    (hS : ∀x y g,‖S.program.run V (x,g)-S.program.run V (y,g)‖≤Ks*‖x-y‖)
    (hEx : ∀x y Y G g,‖E.eval V (x,(Y,G)) g-E.eval V (y,(Y,G)) g‖≤Kx*‖x-y‖)
    (hEy : ∀x Y Z G g,‖E.eval V (x,(Y,G)) g-E.eval V (x,(Z,G)) g‖≤Ky*‖Y-Z‖) :
    ∀x y g,‖(meanParent S E u v T).program.run V (x,g)-(meanParent S E u v T).program.run V (y,g)‖≤
      (Kx+Ky*T*Ks)*‖x-y‖ := by
  intro x y g
  rw [meanParent_run S E u v T V x g,meanParent_run S E u v T V y g]
  have hx := hEx x y (T • S.program.run V (x,leftBlock g)) (middleBlock g 0) (rightBlock g)
  have hy := hEy y (T • S.program.run V (x,leftBlock g)) (T • S.program.run V (y,leftBlock g))
    (middleBlock g 0) (rightBlock g)
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT] at hy
  have hs := mul_le_mul_of_nonneg_left (hS x y (leftBlock g)) (mul_nonneg hKy hT)
  have hn := norm_sub_le_norm_sub_add_norm_sub
    (E.eval V (x,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g))
    (E.eval V (y,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g))
    (E.eval V (y,(T • S.program.run V (y,leftBlock g),middleBlock g 0)) (rightBlock g))
  nlinarith
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling Expression
open scoped Classical BigOperators NNReal

variable {d : ℕ}

theorem terminalReservedProgram_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0≤r) (hl : (lam:ℝ)*r^2≤1/2) (η : ℝ) :
    SquaredAt (gaussianTape d 2) ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (terminalReservedProgram d r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      ((terminalTransportConstant*((lam:ℝ)*r^2))^2*
        (2*(Real.pi*Real.sqrt d+2*r*‖primitiveField F x r 0‖)^2+2*d)) := by
  let f := fullProbabilityFlow hF x hr hl 1
  have hf : Measurable f := (fullProbabilityFlow_lipschitz hF x hr hl ⟨by norm_num,le_rfl⟩).continuous.measurable
  have hm : Measurable (fun z => ‖f z-(z-r • primitiveField F x r z)‖^2) := by
    have hh := (primitiveField_contDiff hF x r).continuous.measurable
    fun_prop
  have hp := terminal_sample_squared_error hF x hr hl
  have hlaw : (gaussianTape d 2).map (fun g => (f (g 0),g 1))=
      (gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)) := by
    have hpair := (measurePreserving_finTwoArrow (stdGaussian (Point d))).map_eq
    have ht := congrArg (Measure.map (Prod.map f id)) hpair
    rw [Measure.map_map (by fun_prop) (by fun_prop),←Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id,hp.1] at ht
    exact ht
  have he (g : Fin 2 → Point d) :
      ‖(terminalReservedProgram d r η).pre.run F (x,g)-
        (f (g 0)+(Real.sqrt 3*η/2) • g 1)‖^2=
      ‖f (g 0)-((g 0)-r • primitiveField F x r (g 0))‖^2 := by
    rw [terminalReservedProgram_pre_run,add_sub_add_right_eq_sub,norm_sub_rev]
    rfl
  apply SquaredAt.of_joint (gaussianTape d 2) (gaussianTape d 2)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
    id (fun g => (f (g 0),g 1)) measurable_id (by fun_prop) Measure.map_id hlaw
    _ _ ?_ (by fun_prop)
  · simpa only [id_eq,he] using gaussianTape_integrable_eval _ hm hp.2.1 (0:Fin 2)
  · simpa only [id_eq,he,gaussianTape_integral_eval _ hm (0:Fin 2)] using hp.2.2
  · have hg := hF.gradient_lipschitz.continuous.measurable
    simp only [terminalReservedProgram_pre_run]
    fun_prop

lemma terminalReservedProgram_equivariant (r η : ℝ) (Δ : Point d) :
    (terminalReservedProgram d r η).pre.Equivariant
      (moveSeed (fun x => x+r • Δ) (terminalReservedProgram d r η).shift Δ) (fun y => y-Δ) := by
  change (oneQuery (fun p : Point d × (Fin 2 → Point d) => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop)).Equivariant _ _
  apply Program.oneQuery_equivariant
  · intro p
    simp [moveSeed,shiftSlots,terminalReservedProgram,SeedCompiler.terminalShift]
    module
  · intro p z
    simp [moveSeed,shiftSlots,terminalReservedProgram,SeedCompiler.terminalShift]
    module

lemma terminalReservedProgram_lipschitz (r η : ℝ) {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) : ∀x y g,
    ‖(terminalReservedProgram d r η).pre.run F (x,g)-(terminalReservedProgram d r η).pre.run F (y,g)‖≤
      |r| *(lam:ℝ)*‖x-y‖ := by
  intro x y g
  change Fin 2 → Point d at g
  rw [terminalReservedProgram_pre_run r η F x g,terminalReservedProgram_pre_run r η F y g,add_sub_add_right_eq_sub]
  have he : g 0-r • gradient F (x+r • g 0)-(g 0-r • gradient F (y+r • g 0))=
      (-r) • (gradient F (x+r • g 0)-gradient F (y+r • g 0)) := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg]
  have hh := hF.gradient_lipschitz.dist_le_mul (x+r • g 0) (y+r • g 0)
  rw [dist_eq_norm,dist_eq_norm,add_sub_add_right_eq_sub] at hh
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg r)).trans_eq (by ring)

end LogConcaveSampling

end

end

end OAI
