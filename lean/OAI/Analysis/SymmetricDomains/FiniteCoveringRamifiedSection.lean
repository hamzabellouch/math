import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Function

theorem finite_covering_lift_period
    {A X E : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p) (f : A → X)
    (σ : A ≃ₜ A) (hσ : ∀ a, f (σ a) = f a)
    (g : A → E) (hg : Continuous g) (hpg : p ∘ g = f)
    (a : A) (hfinite : (p ⁻¹' {f a}).Finite) :
    ∃ l : ℕ, 0 < l ∧ ∀ x, g (σ^[l] x) = g x := by
  classical
  have hfiter (k : ℕ) (x : A) : f (σ^[k] x) = f x := by
    induction k with
    | zero => rfl
    | succ k hk => simpa only [Function.iterate_succ_apply',hσ] using hk
  let v : ℕ → p ⁻¹' {f a} := fun k => ⟨g (σ^[k] a),by
    change p (g (σ^[k] a)) = f a
    rw [show p (g (σ^[k] a)) = f (σ^[k] a) from congrFun hpg _]
    exact hfiter k a⟩
  let : Finite (p ⁻¹' {f a}) := hfinite.to_subtype
  obtain ⟨i,j,hij,hv⟩ : ∃ i j : ℕ, i < j ∧ v i = v j := by
    obtain ⟨i,j,hne,hv⟩ := Finite.exists_ne_map_eq_of_infinite v
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i,j,h,hv⟩
    · exact ⟨j,i,h,hv.symm⟩
  have hbase : g (σ^[i] a) = g (σ^[j] a) := congrArg Subtype.val hv
  have heq : (fun x => g (σ^[i] x)) = (fun x => g (σ^[j] x)) := by
    apply hp.eq_of_comp_eq (hg.comp (σ.continuous.iterate i))
      (hg.comp (σ.continuous.iterate j)) _ a hbase
    funext x
    change p (g (σ^[i] x)) = p (g (σ^[j] x))
    rw [show p (g (σ^[i] x)) = f (σ^[i] x) from congrFun hpg _,
      show p (g (σ^[j] x)) = f (σ^[j] x) from congrFun hpg _,hfiter,hfiter]
  refine ⟨j-i,Nat.sub_pos_of_lt hij,fun x => ?_⟩
  obtain ⟨y,hy⟩ := σ.surjective.iterate i x
  have h := congrFun heq y
  have hj : j = (j-i)+i := by omega
  rw [hj,Function.iterate_add_apply,hy] at h
  exact h.symm

open Complex
open scoped UpperHalfPlane
open Function.Periodic

def PuncturedUnitDisk := {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1}

instance : TopologicalSpace PuncturedUnitDisk := inferInstanceAs (TopologicalSpace {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1})

noncomputable def halfPlaneQ (h : ℝ) (hh : 0 < h) (z : ℍ) : PuncturedUnitDisk :=
  ⟨qParam h z,qParam_ne_zero (h := h) z,norm_qParam_lt_one hh z.im_pos⟩

theorem continuous_halfPlaneQ (h : ℝ) (hh : 0 < h) : Continuous (halfPlaneQ h hh) :=
  ((continuous_qParam (h := h)).comp UpperHalfPlane.continuous_coe).subtype_mk _

noncomputable def halfPlaneInvQ (h : ℝ) (hh : 0 < h) (q : PuncturedUnitDisk) : ℍ :=
  ⟨invQParam h q.val,by
    apply (norm_qParam_lt_iff hh 0 _).mp
    simpa only [qParam_right_inv hh.ne' q.property.1,mul_zero,zero_div,Real.exp_zero] using q.property.2⟩

theorem halfPlaneQ_right_inv (h : ℝ) (hh : 0 < h) (q : PuncturedUnitDisk) :
    halfPlaneQ h hh (halfPlaneInvQ h hh q) = q := by
  apply Subtype.ext
  exact qParam_right_inv hh.ne' q.property.1

theorem isOpenMap_halfPlaneQ (h : ℝ) (hh : 0 < h) : IsOpenMap (halfPlaneQ h hh) := by
  have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  apply hopen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  have ha : 2 * Real.pi * I / (h : ℂ) ≠ 0 :=
    div_ne_zero two_pi_I_ne_zero (ofReal_ne_zero.mpr hh.ne')
  have H := Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ ha).isOpenMap
  have H' := H.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  convert H' using 1
  ext z
  change exp (2 * ↑Real.pi * I * (z : ℂ) / ↑h) = exp ((2 * ↑Real.pi * I / ↑h) * z)
  congr 1
  ring

theorem isOpenQuotientMap_halfPlaneQ (h : ℝ) (hh : 0 < h) :
    IsOpenQuotientMap (halfPlaneQ h hh) :=
  ⟨fun q => ⟨halfPlaneInvQ h hh q,halfPlaneQ_right_inv h hh q⟩,
    continuous_halfPlaneQ h hh,isOpenMap_halfPlaneQ h hh⟩

noncomputable def halfPlaneShift (a : ℝ) : ℍ ≃ₜ ℍ where
  toFun z := a +ᵥ z
  invFun z := (-a) +ᵥ z
  left_inv z := by simp [← add_vadd]
  right_inv z := by simp [← add_vadd]
  continuous_toFun := (continuous_const.add UpperHalfPlane.continuous_coe).upperHalfPlaneMk _
  continuous_invFun := (continuous_const.add UpperHalfPlane.continuous_coe).upperHalfPlaneMk _

theorem halfPlaneQ_shift (h : ℝ) (hh : 0 < h) (z : ℍ) :
    halfPlaneQ h hh (halfPlaneShift h z) = halfPlaneQ h hh z := by
  apply Subtype.ext
  change exp (2 * ↑Real.pi * I * ((h : ℂ) + (z : ℂ)) / ↑h) = exp (2 * ↑Real.pi * I * (z : ℂ) / ↑h)
  rw [show 2 * ↑Real.pi * I * ((h : ℂ) + (z : ℂ)) / ↑h =
    2 * ↑Real.pi * I * (z : ℂ) / ↑h + 2 * ↑Real.pi * I by field_simp [ofReal_ne_zero.mpr hh.ne']; ring]
  exact Complex.exp_periodic _

theorem halfPlaneShift_iterate (a : ℝ) (l : ℕ) (z : ℍ) :
    (halfPlaneShift a)^[l] z = halfPlaneShift (l*a) z := by
  induction l with
  | zero => apply UpperHalfPlane.ext; simp [halfPlaneShift]
  | succ l hl =>
    rw [Function.iterate_succ_apply',hl]
    apply UpperHalfPlane.ext
    change (a : ℂ) + ((((l : ℝ)*a : ℝ) : ℂ) + (z : ℂ)) =
      ((((l+1 : ℕ) : ℝ)*a : ℝ) : ℂ) + (z : ℂ)
    push_cast
    ring

theorem halfPlaneShift_add (a b : ℝ) (z : ℍ) :
    halfPlaneShift (a+b) z = halfPlaneShift a (halfPlaneShift b z) := by
  apply UpperHalfPlane.ext
  change ((a+b : ℝ) : ℂ) + (z : ℂ) = (a : ℂ) + ((b : ℂ) + (z : ℂ))
  push_cast
  ring

theorem halfPlaneShift_zero (z : ℍ) : halfPlaneShift 0 z = z := by
  apply UpperHalfPlane.ext
  change (0 : ℂ) + (z : ℂ) = (z : ℂ)
  simp

theorem halfPlane_period_descent {S E : Type*} [TopologicalSpace S] [TopologicalSpace E]
    (h : ℝ) (hh : 0 < h) (g : S × ℍ → E) (hg : Continuous g)
    (hper : ∀ s z, g (s,halfPlaneShift h z) = g (s,z)) :
    ∃ G : S × PuncturedUnitDisk → E, Continuous G ∧
      ∀ s z, G (s,halfPlaneQ h hh z) = g (s,z) := by
  let G : S × PuncturedUnitDisk → E := fun x => g (x.1,halfPlaneInvQ h hh x.2)
  have hG (s : S) (z : ℍ) : G (s,halfPlaneQ h hh z) = g (s,z) := by
    obtain ⟨m,hm⟩ := qParam_left_inv_mod_period hh.ne' (z : ℂ)
    have he : halfPlaneInvQ h hh (halfPlaneQ h hh z) = halfPlaneShift ((m : ℝ)*h) z := by
      apply UpperHalfPlane.ext
      change invQParam h (qParam h z) = (((m : ℝ)*h : ℝ) : ℂ) + (z : ℂ)
      rw [hm]
      push_cast
      ring
    have hp : Periodic (fun a : ℝ => g (s,halfPlaneShift a z)) h := by
      intro a
      change g (s,halfPlaneShift (a+h) z) = g (s,halfPlaneShift a z)
      rw [add_comm a h,halfPlaneShift_add,hper]
    dsimp only [G]
    rw [he]
    simpa only [halfPlaneShift_zero] using hp.int_mul_eq m
  refine ⟨G,?_,hG⟩
  have hQ : IsOpenQuotientMap (Prod.map (id : S → S) (halfPlaneQ h hh)) :=
    IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_halfPlaneQ h hh)
  apply hQ.isQuotientMap.continuous_iff.mpr
  convert hg using 1
  funext x
  exact hG x.1 x.2

noncomputable def puncturedPower (l : ℕ) (hl : 0 < l) (q : PuncturedUnitDisk) :
    PuncturedUnitDisk :=
  ⟨q.val^l,pow_ne_zero l q.property.1,by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) q.property.2 hl.ne'⟩

theorem halfPlaneQ_nat (l : ℕ) (hl : 0 < l) (z : ℍ) :
    halfPlaneQ 1 one_pos z = puncturedPower l hl (halfPlaneQ l (by exact_mod_cast hl) z) := by
  apply Subtype.ext
  change exp (2 * ↑Real.pi * I * (z : ℂ) / (1 : ℂ)) =
    exp (2 * ↑Real.pi * I * (z : ℂ) / (l : ℂ))^l
  rw [← exp_nat_mul]
  congr 1
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp

theorem finite_covering_ramified_section {S E : Type*}
    [TopologicalSpace S] [ContractibleSpace S] [LocallyPathConnectedSpace S]
    [TopologicalSpace E]
    (p : E → S × PuncturedUnitDisk) (hp : IsCoveringMap p)
    (s₀ : S) (z₀ : ℍ) (e₀ : E) (he : p e₀ = (s₀,halfPlaneQ 1 one_pos z₀))
    (hfinite : (p ⁻¹' {(s₀,halfPlaneQ 1 one_pos z₀)}).Finite) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ G : S × PuncturedUnitDisk → E,
      Continuous G ∧ (∀ s q, p (G (s,q)) = (s,puncturedPower l hl q)) ∧
        G (s₀,halfPlaneQ l (by exact_mod_cast hl) z₀) = e₀ := by
  let f : C(S × ℍ,S × PuncturedUnitDisk) :=
    ⟨Prod.map id (halfPlaneQ 1 one_pos),continuous_id.prodMap (continuous_halfPlaneQ 1 one_pos)⟩
  obtain ⟨g,⟨hbase,hpg⟩,_⟩ := hp.existsUnique_continuousMap_lifts f (s₀,z₀) e₀ he
  let σ : (S × ℍ) ≃ₜ (S × ℍ) := (Homeomorph.refl S).prodCongr (halfPlaneShift 1)
  have hσ : ∀ x, f (σ x) = f x := by
    intro x
    change (x.1,halfPlaneQ 1 one_pos (halfPlaneShift 1 x.2)) = (x.1,halfPlaneQ 1 one_pos x.2)
    rw [halfPlaneQ_shift]
  obtain ⟨l,hl,hper⟩ := finite_covering_lift_period p hp f σ hσ g g.continuous hpg
    (s₀,z₀) hfinite
  have hiter (n : ℕ) (s : S) (z : ℍ) : σ^[n] (s,z) = (s,(halfPlaneShift 1)^[n] z) := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply',hn,Function.iterate_succ_apply']; rfl
  have hperiod (s : S) (z : ℍ) : g (s,halfPlaneShift (l : ℝ) z) = g (s,z) := by
    simpa only [hiter,halfPlaneShift_iterate,mul_one] using hper (s,z)
  obtain ⟨G,hGc,hG⟩ := halfPlane_period_descent (l : ℝ) (by exact_mod_cast hl) g g.continuous hperiod
  refine ⟨l,hl,G,hGc,?_,(hG s₀ z₀).trans hbase⟩
  intro s q
  obtain ⟨z,hz⟩ := (isOpenQuotientMap_halfPlaneQ (l : ℝ) (by exact_mod_cast hl)).surjective q
  rw [← hz,hG]
  have hc := congrFun hpg (s,z)
  change p (g (s,z)) = (s,halfPlaneQ 1 one_pos z) at hc
  exact hc.trans (congrArg (s,·) (halfPlaneQ_nat l hl z))

end Release061

end

end OAI
