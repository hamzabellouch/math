import OAI.Probability.GaussianReplacement.StreamLearner

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection







namespace StreamKernel
open unitInterval

section BorelVersion
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Nonempty Y] {μ : Measure X} (f : X → Measure Y)
  (hf : AEMeasurable f μ) (hp : ∀ x, IsProbabilityMeasure (f x))



def borelKernel : Kernel X Y :=
  ⟨fun x => if hf.mk f x Set.univ = 1 then hf.mk f x
        else Measure.dirac (Classical.choice ‹Nonempty Y›),
    hf.measurable_mk.ite
      (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp
        hf.measurable_mk) measurable_const) measurable_const⟩

instance borelKernel_markov : IsMarkovKernel (borelKernel f hf) := by
  constructor
  intro x
  dsimp [borelKernel]
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

lemma borelKernel_ae (hp : ∀ x, IsProbabilityMeasure (f x)) : ∀ᵐ x ∂μ, borelKernel f hf x = f x := by
  filter_upwards [hf.ae_eq_mk] with x hx
  have h : hf.mk f x Set.univ = 1 := by
    rw [← hx]
    exact (hp x).measure_univ
  change (if hf.mk f x Set.univ = 1 then hf.mk f x else _) = f x
  rw [ite_eq_left h, ← hx]
end BorelVersion


abbrev Coins (n : ℕ) := Fin (n+1) → I

def coinLaw (n : ℕ) : Measure (Coins n) := Measure.pi fun _ => (volume : Measure I)
instance coinLaw_probability (n : ℕ) : IsProbabilityMeasure (coinLaw n) := by
  unfold coinLaw
  infer_instance

section Fold
variable {A : Type*} [MeasurableSpace A]
  (initial : I → A) (step : ℕ → A → I → A)

def foldCoins : (n : ℕ) → Coins n → A
  | 0, z => initial (z 0)
  | n+1, z => step (n+1) (foldCoins n (Fin.init z)) (z (Fin.last (n+1)))

lemma measurable_foldCoins (hi : Measurable initial)
    (hs : ∀ n, Measurable (Function.uncurry (step n))) (n : ℕ) :
    Measurable (foldCoins initial step n) := by
  induction n with
  | zero => exact hi.comp (measurable_pi_apply 0)
  | succ n ih =>
    exact (hs (n+1)).comp
      ((ih.comp (Measurable.of_eval fun i => measurable_pi_apply i.castSucc)).prodMk
        (measurable_pi_apply (Fin.last (n+1))))

lemma coinLaw_split (n : ℕ) :
    (coinLaw (n+1)).map (fun z => (z (Fin.last (n+1)), Fin.init z)) =
      (volume : Measure I).prod (coinLaw n) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+2) => (volume : Measure I)) (Fin.last (n+1))).map_eq
  have he : (fun z : Coins (n+1) => (z (Fin.last (n+1)), Fin.init z)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => I) (Fin.last (n+1))) := by
    funext z
    simp [MeasurableEquiv.piFinSuccAbove, Fin.init_def]
  rw [he]
  exact h

lemma map_freshCoin {B : Type*} [MeasurableSpace B] (n : ℕ)
    (state : Coins n → A) (out : A → I → B)
    (hstate : Measurable state) (ho : Measurable (Function.uncurry out)) :
    (coinLaw (n+1)).map (fun z => out (state (Fin.init z)) (z (Fin.last (n+1)))) =
      ((coinLaw n).map state).bind (fun a => (volume : Measure I).map (out a)) := by
  have hk : Measurable (fun a => (volume : Measure I).map (out a)) :=
    by
      apply Measure.measurable_of_measurable_coe
      intro s hs'
      simp_rw [Measure.map_apply (ho).of_uncurry_left hs']
      exact measurable_measure_prodMk_left ((ho) hs')
  apply Measure.ext_of_lintegral
  intro f hf
  have hall : Measurable (fun z : Coins (n+1) =>
      out (state (Fin.init z)) (z (Fin.last (n+1)))) :=
    ho.comp ((hstate.comp (Measurable.of_eval fun i =>
      measurable_pi_apply i.castSucc)).prodMk (measurable_pi_apply (Fin.last (n+1))))
  rw [lintegral_map hf hall,
    Measure.lintegral_bind hk.aemeasurable hf.aemeasurable,
    lintegral_map _ hstate]
  · have hfun : Measurable (fun z : I × Coins n =>
        f (out (state z.2) z.1)) :=
      hf.comp ((ho).comp ((hstate.comp measurable_snd).prodMk measurable_fst))
    have he := lintegral_map (μ:=coinLaw (n+1)) hfun
      (show Measurable (fun z : Coins (n+1) =>
        (z (Fin.last (n+1)), Fin.init z)) from
        (measurable_pi_apply _).prodMk
          (Measurable.of_eval fun i => measurable_pi_apply i.castSucc))
    rw [coinLaw_split] at he
    rw [← he, lintegral_prod_symm _ hfun.aemeasurable]
    apply lintegral_congr
    intro z
    rw [lintegral_map hf ((ho).of_uncurry_left)]
  · exact (Measure.measurable_lintegral hf).comp hk

lemma map_foldCoins_succ (hi : Measurable initial)
    (hs : ∀ n, Measurable (Function.uncurry (step n))) (n : ℕ) :
    (coinLaw (n+1)).map (foldCoins initial step (n+1)) =
      ((coinLaw n).map (foldCoins initial step n)).bind
        (fun a => (volume : Measure I).map (step (n+1) a)) := by
  exact map_freshCoin n (foldCoins initial step n) (step (n+1))
    (measurable_foldCoins initial step hi hs n) (hs (n+1))

end Fold
end StreamKernel




end CurrentProjection

end

end OAI
