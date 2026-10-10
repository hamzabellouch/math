import OAI.Analysis.C0Absorption.Tests

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def BoundedTest (f : S → ℝ) : Prop :=
  ∃ K : ℝ≥0, ∀ m : PreSpace L o, |pairing S f m| ≤ K*‖m‖

theorem class_pairing_bound (j : ℕ) (K : ℝ≥0)
    (hK : ∀ f ∈ L j, LipschitzWith K f) :
    ∃ A : ℝ≥0, ∀ f ∈ L j, ∀ m : PreSpace L o, |pairing S f m| ≤ A*‖m‖ := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨n,hn⟩ := triple_surjective (j,C,0)
  refine ⟨(squareWeight n)⁻¹,?_⟩
  intro f hf m
  apply test_pairing_bound L o n f
  · simpa only [hn] using hf
  · apply (hK f hf).weaken
    change K ≤ ((triple n).2.1 : ℝ≥0)+1
    rw [hn]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)

theorem BoundedTest.continuous {f : S → ℝ} (hf : BoundedTest L o f) :
    Continuous (completedPairing L o f) := by
  obtain ⟨K,hK⟩ := hf
  exact (completedPairing_lipschitz L o f K hK).continuous

theorem BoundedTest.weak_null {f : S → ℝ} (hf : BoundedTest L o f)
    (m : ℕ → TestSpace L o) (M : ℝ)
    (hm : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Tendsto (fun i => completedPairing L o f (m i)) atTop (nhds 0) := by
  obtain ⟨K,hK⟩ := hf
  simpa only [completedTest_eq] using bounded_signs_weak_null m M hm (completedTest L o f K hK)

theorem pairing_add {S : Type*} [MetricSpace S]
    (f g : S → ℝ) (m : Molecule S) :
    pairing S (fun s => f s+g s) m = pairing S f m+pairing S g m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum, Finset.sum_add_distrib]

theorem pairing_smul {S : Type*} [MetricSpace S]
    (a : ℝ) (f : S → ℝ) (m : Molecule S) :
    pairing S (fun s => a*f s) m = a*pairing S f m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem BoundedTest.add {f g : S → ℝ} (hf : BoundedTest L o f) (hg : BoundedTest L o g) :
    BoundedTest L o (fun s => f s+g s) := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  refine ⟨K+A,fun m => ?_⟩
  erw [pairing_add]
  exact (abs_add_le _ _).trans ((add_le_add (hK m) (hA m)).trans_eq (by push_cast; ring))

theorem BoundedTest.smul {f : S → ℝ} (hf : BoundedTest L o f) (a : ℝ) :
    BoundedTest L o (fun s => a*f s) := by
  obtain ⟨K,hK⟩ := hf
  refine ⟨‖a‖₊*K,fun m => ?_⟩
  erw [pairing_smul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hK m) (abs_nonneg a)).trans_eq (by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]; ring)

theorem completedPairing_add (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  obtain ⟨B,hB⟩ := (BoundedTest.add L o ⟨K,hK⟩ ⟨A,hA⟩)
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      ((completedPairing_lipschitz L o _ K hK).continuous.add (completedPairing_lipschitz L o _ A hA).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK,
      completedPairing_coe L o _ A hA]
    exact pairing_add f g m

theorem completedPairing_smul (a : ℝ) (f : S → ℝ) (hf : BoundedTest L o f)
    (z : TestSpace L o) : completedPairing L o (fun s => a*f s) z = a*completedPairing L o f z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨B,hB⟩ := BoundedTest.smul L o ⟨K,hK⟩ a
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      (continuous_const.mul (completedPairing_lipschitz L o _ K hK).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK]
    exact pairing_smul a f m

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

def c0Origin : C0Ball := ⟨0,by simp⟩
abbrev SourceSpace (B : CylinderBases Γ) := TestSpace (sourceClasses B) c0Origin

theorem TClass_mono {h k : ℕ} (hk : h ≤ k) : TClass B h ⊆ TClass B k := by
  rintro f ⟨γ,r,hr,rfl⟩
  exact ⟨γ,r,hr.trans hk,rfl⟩

theorem VClass_mono {h k : ℕ} (hk : h ≤ k) : VClass B h ⊆ VClass B k := by
  rintro f ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩
  exact ⟨γ,r,ts,hr.trans hk,hj.trans hk,ht.trans hk,fun t hm => (hs t hm).trans hk,rfl⟩

theorem representation_mem_VClass {γ : Γ} (r : GeneratedRepresentation B γ) {h : ℕ}
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) : r.value ∈ VClass B h := by
  refine ⟨γ,r,[],hr,hj,by simp,by simp,?_⟩
  funext s
  simp

theorem sourceClasses_lipschitz (B : CylinderBases Γ) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ f ∈ sourceClasses B n, LipschitzWith K f := by
  unfold sourceClasses
  split
  · exact ⟨_, fun _ hf => TClass_lipschitz B _ hf⟩
  · exact ⟨_, fun _ hf => VClass_lipschitz B _ hf⟩

theorem TClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ TClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h) (4^(h+1)*B.L0) (by
    simpa only [sourceClasses_even] using (fun f hf => TClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_even] using TClass_mono (Nat.le_succ h) hf)⟩

theorem VClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ VClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) (by
      simpa only [sourceClasses_odd, Nat.cast_add, Nat.cast_one] using (fun f hf => VClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) hf)⟩

theorem TClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ TClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := TClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

theorem VClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := VClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def flattenOperation (I : Finset ℕ) (a : ℕ) (v : Cube I) : CylinderOperation I :=
  ⟨a,nearestOperationGrid I a v,true⟩

@[simp] theorem flattenOperation_scale (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    (flattenOperation I a v).scale = dyadic a := rfl

@[simp] theorem flattenOperation_act (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ) :
    (flattenOperation I a v).act u = localG (flattenOperation I a v).point (dyadic a) u := rfl

theorem flattenOperation_center (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    dist v (flattenOperation I a v).point ≤ dyadic a/16 := nearestOperationGrid_dist I a v

theorem flattenOperation_plateau (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ)
    (x : Cube I) (hx : dist x v < 3*dyadic a/8) :
    (flattenOperation I a v).act u x = u (flattenOperation I a v).point := by
  apply localG_plateau _ (dyadic_pos a) u x
  have hh := dist_triangle x v (flattenOperation I a v).point
  have hc := flattenOperation_center I a v
  linarith [dyadic_pos a]

theorem flattenOperation_difference (I : Finset ℕ) (a : ℕ) (v : Cube I)
    {u : Cube I → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (x : Cube I) :
    |(flattenOperation I a v).act u x-u x| ≤ dyadic a*K := by
  rw [flattenOperation_act, localG_eq, add_sub_cancel_left]
  exact localR_sup_lip _ (dyadic_pos a) u hu x

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem exists_flatten (r : GeneratedRepresentation B γ) (ts : List TailOperation)
    (h : ℕ) (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ts.length ≤ h) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin (fun s => r'.value s*tailProduct ts s) z-
        completedPairing (sourceClasses B) c0Origin (fun s => r.value s*tailProduct ts s) z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s*tailProduct ts s
  let g (s : C0Ball) := r.value s*tailProduct ts s
  have hf (n : ℕ) : f n ∈ VClass B (h+1) := by
    refine ⟨γ,rr n,ts,?_,hj.trans (Nat.le_succ h),ht.trans (Nat.le_succ h),
      fun t hm => (hs t hm).trans (Nat.le_succ h),rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      simp only [f,g,Real.dist_eq,← sub_mul,abs_mul]
      have hd : |(rr n).value s-r.value s| ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
        change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
        rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
        exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
      exact (mul_le_mul hd (tailProduct_abs_le ts s) (abs_nonneg _) (mul_nonneg (dyadic_pos _).le (NNReal.coe_nonneg _))).trans_eq (mul_one _)
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := VClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

theorem exists_flatten_T (r : GeneratedRepresentation B γ)
    (h : ℕ) (hr : r.operations.length ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin r'.value z-
        completedPairing (sourceClasses B) c0Origin r.value z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s
  let g (s : C0Ball) := r.value s
  have hf (n : ℕ) : f n ∈ TClass B (h+1) := by
    refine ⟨γ,rr n,?_,rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
      rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
      exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := TClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

end GeneratedRepresentation
end
end C0Absorption

end OAI
