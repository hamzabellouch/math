import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoiseTensor
open Classical MeasureTheory

noncomputable def noiseTensor {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ)
    (x : ι → ℝ) : ℝ := ∏i,u i (x i)

theorem noiseTensor_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x*noiseTensor v x ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t*v i t := by
  simp only [noiseTensor,← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => u i x*v i x)

theorem noiseTensor_integrable_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ)
    (h : ∀i,Integrable (fun t : ℝ => u i t*v i t)) :
    Integrable (fun x : ι → ℝ => noiseTensor u x*noiseTensor v x) (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  simpa only [noiseTensor,← Finset.prod_mul_distrib] using Integrable.fintype_prod h

theorem noiseTensor_energy {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t^2 := by
  simpa only [pow_two] using noiseTensor_inner u u

noncomputable def centeredNoiseTensor {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (s : Finset ι) (u : ι → ℝ → ℝ) : (ι → ℝ) → ℝ :=
  noiseTensor (fun i => if i∈s then u i else f)

theorem centeredNoiseTensor_orthogonal {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (s t : Finset ι) (u v : ι → ℝ → ℝ)
    (hu : ∀i∈s,(∫x : ℝ,u i x*f x)=0)
    (hv : ∀i∈t,(∫x : ℝ,v i x*f x)=0) (hne : s≠t) :
    (∫x : ι → ℝ,centeredNoiseTensor f s u x*centeredNoiseTensor f t v x ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=0 := by
  rw [centeredNoiseTensor,centeredNoiseTensor,noiseTensor_inner]
  obtain ⟨i,hi⟩ := not_forall.mp (Finset.ext_iff.not.mp hne)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hs : i∈s
  · have ht : i∉t := by tauto
    simpa only [ite_eq_left hs,ite_eq_right ht] using hu i hs
  · have ht : i∈t := by tauto
    simpa only [ite_eq_right hs,ite_eq_left ht,mul_comm] using hv i ht

theorem centeredNoiseTensor_energy {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : (∫x : ℝ,f x^2)=1) (s : Finset ι) (u : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,centeredNoiseTensor f s u x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i∈s,∫t : ℝ,u i t^2 := by
  rw [centeredNoiseTensor,noiseTensor_energy]
  calc
    _ = ∏i : ι,if i∈s then (∫t : ℝ,u i t^2) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      split_ifs with hi
      · rfl
      · exact hf
    _ = _ := by simp

end NoiseTensor

section NoiseMoments
open Classical MeasureTheory

inductive NoiseFactor
  | base | score | position | diagonal
  deriving DecidableEq

noncomputable def noiseFactor (f : ℝ → ℝ) : NoiseFactor → ℝ → ℝ
  | .base => f
  | .score => deriv f
  | .position => fun x => x*f x
  | .diagonal => fun x => x*deriv f x+f x/2

theorem noiseFactor_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : NoiseFactor) :
    Continuous (noiseFactor f i) := by
  have hc := hf.continuous
  have hd := hf.continuous_deriv le_rfl
  cases i <;> dsimp [noiseFactor] <;> fun_prop

theorem noiseFactor_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (i : NoiseFactor) :
    HasCompactSupport (noiseFactor f i) := by
  cases i
  · exact hf
  · exact hf.deriv
  · exact hf.mul_left
  · have hh : HasCompactSupport (fun x => f x/2) := by
      convert! (hf.mul_right (f':=fun _ => (2:ℝ)⁻¹)) using 1
    exact hf.deriv.mul_left.add hh

theorem noiseFactor_integrable_product {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i j : NoiseFactor) :
    Integrable (fun x => noiseFactor f i x*noiseFactor f j x) :=
  ((noiseFactor_continuous hf i).mul (noiseFactor_continuous hf j)).integrable_of_hasCompactSupport
    (noiseFactor_compact hc i).mul_right

theorem noiseFactor_centered {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (he : Function.Even f) (i : NoiseFactor) (hi : i≠.base) :
    (∫x : ℝ,noiseFactor f i x*f x)=0 := by
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x := (hf.differentiable (by norm_num) x).hasDerivAt
  have hff := noiseFactor_integrable_product hf hc .base .base
  have hfd := noiseFactor_integrable_product hf hc .base .score
  have hdf := noiseFactor_integrable_product hf hc .score .base
  dsimp only [noiseFactor] at hff hfd hdf
  cases i
  · exact (hi rfl).elim
  · have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hd x) (fun x _ => hd x) hfd hdf hff
    have heq : (∫x : ℝ,f x*deriv f x)=(∫x : ℝ,deriv f x*f x) := by
      congr 1
      funext x
      ring
    dsimp [noiseFactor] at h ⊢
    linarith
  · have h := integral_neg_eq_self (fun x : ℝ => x*f x*f x) volume
    have heq : (fun x : ℝ => (-x)*f (-x)*f (-x))=(fun x : ℝ => -(x*f x*f x)) := by
      funext x
      rw [he x]
      ring
    change (∫x : ℝ,(-x)*f (-x)*f (-x))=(∫x : ℝ,x*f x*f x) at h
    rw [heq,integral_neg] at h
    dsimp [noiseFactor]
    linarith
  · have hup (x : ℝ) : HasDerivAt (fun x => x*f x) (f x+x*deriv f x) x := by
      convert! (hasDerivAt_id x).mul (hd x) using 1; simp only [one_mul,id_eq]
    have hp := noiseFactor_integrable_product hf hc .position .score
    have hp₀ := noiseFactor_integrable_product hf hc .position .base
    dsimp only [noiseFactor] at hp hp₀
    have hp' : Integrable (fun x : ℝ => (f x+x*deriv f x)*f x) := by
      have hj := noiseFactor_integrable_product hf hc .diagonal .base
      apply (hj.add (hff.div_const 2)).congr
      filter_upwards with x
      dsimp [noiseFactor]
      ring
    have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hup x) (fun x _ => hd x) hp hp' hp₀
    let I := ∫x : ℝ,x*f x*deriv f x
    have hright : (∫x : ℝ,(f x+x*deriv f x)*f x)=(∫x : ℝ,f x*f x)+I := by
      have hi : Integrable (fun x : ℝ => x*deriv f x*f x) := by
        apply hp.congr
        filter_upwards with x
        ring
      rw [show (fun x : ℝ => (f x+x*deriv f x)*f x)=
        (fun x : ℝ => f x*f x+x*deriv f x*f x) by ext x; ring,integral_add hff hi]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    change I=-(∫x : ℝ,(f x+x*deriv f x)*f x) at h
    rw [hright] at h
    have hgoal : (∫x : ℝ,noiseFactor f .diagonal x*f x)=I+(∫x : ℝ,f x*f x)/2 := by
      have hi : Integrable (fun x : ℝ => x*f x*deriv f x) := hp
      have hb : Integrable (fun x : ℝ => (f x*f x)/2) := hff.div_const 2
      rw [show (fun x : ℝ => noiseFactor f .diagonal x*f x)=
        (fun x : ℝ => x*f x*deriv f x+(f x*f x)/2) by ext x; dsimp [noiseFactor]; ring,
        integral_add hi hb,integral_div]
    rw [hgoal]
    linarith

end NoiseMoments

end SimpleAmenable
end
end

end OAI
