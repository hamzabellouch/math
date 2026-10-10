import OAI.NumberTheory.Ostmann.Characters.UniformFinite

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction

theorem few_bad_endpoints {ι α:Type*} [Fintype ι] [DecidableEq α]
    (S:Finset α) (μ:FinitePrior ι) (f:ι→α→ℂ) (z:ι→ℂ)
    (T δ ε:ℝ) (hT:0<T) (hδ:0<δ) (hε:ε<(δ/2)^2)
    (hz:δ≤(μ.cmean z).re)
    (hstab:∀ U:Finset α,U⊆S→T≤(U.card:ℝ)→
      μ.mean (fun p=>‖(∑a∈U,f p a)/(U.card:ℂ)-z p‖^2)≤ε) :
    ((S.filter (fun a=>(μ.cmean (fun p=>f p a)).re<δ/2)).card:ℝ)<T := by
  classical
  let U := S.filter (fun a=>(μ.cmean (fun p=>f p a)).re<δ/2)
  by_contra hn
  have hcard : T≤(U.card:ℝ) := le_of_not_gt hn
  have hpos : (0:ℝ)<U.card := hT.trans_le hcard
  have hU : U.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  let ν := uniformPrior U hU
  let av : ι→ℂ := fun p=>ν.cmean (fun a=>f p a.val)
  have hav (p:ι) : av p=(∑a∈U,f p a)/(U.card:ℂ) := uniformPrior_cmean U hU (f p)
  have hbad : (μ.cmean av).re≤δ/2 := by
    rw [show μ.cmean av=ν.cmean (fun a=>μ.cmean (fun p=>f p a.val)) from
      prior_cmean_comm μ ν (fun p a=>f p a.val), prior_cmean_re]
    apply le_trans (ν.mean_mono (fun a => (Finset.mem_filter.mp a.property).2.le))
    exact ν.mean_const (δ/2) |>.le
  have hgap : δ/2≤(μ.cmean (fun p=>z p-av p)).re := by
    rw [prior_cmean_sub, Complex.sub_re]
    linarith
  have hsquare := μ.norm_cmean_sq_le (fun p=>z p-av p)
  have hnorm : δ/2≤‖μ.cmean (fun p=>z p-av p)‖ := hgap.trans (Complex.re_le_norm _)
  have herror : μ.mean (fun p=>‖z p-av p‖^2)≤ε := by
    simpa only [hav, norm_sub_rev] using hstab U (Finset.filter_subset _ _) hcard
  have hd : 0≤δ/2 := by positivity
  have hlow := pow_le_pow_left₀ hd hnorm 2
  linarith

end Ostmann.Characters

end

end OAI
