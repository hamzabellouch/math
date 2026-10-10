import OAI.Combinatorics.HoneycombChords.SpectralRows
import OAI.Combinatorics.HoneycombChords.YangBaxter

namespace OAI

/-!
# Spectral commutation for critical honeycomb strips

Formalized from *Uniform marked polygon estimates and sharp finite bridge moments*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.Transfer.RowExchange
open YangBaxter
open scoped Matrix BigOperators
noncomputable def sourceMatrix (u : ℝ) : Local := sourceR u
lemma local_source_exchange (u v : ℝ)
    (hu : YangBaxter.denominator u≠0) (hv : YangBaxter.denominator v≠0) (hd : YangBaxter.denominator (u-v)≠0)
    (s t : Spin) : sourceMatrix (u-v)*localForward (sourceR u) (sourceR v) s t=
      localBackward (sourceR u) (sourceR v) s t*sourceMatrix (u-v) := by
  ext ⟨a,b⟩ ⟨d,e⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,localForward,localBackward,
    Matrix.kronecker,Matrix.kroneckerMap,block,Matrix.sum_apply,Matrix.of_apply,
    Finset.mul_sum,Finset.sum_mul]
  simp only [sourceMatrix]
  have hh:=source_yang_baxter u v hu hv hd a b s d e t
  convert hh using 1 <;>
    (apply Finset.sum_congr rfl;intro j hj
     apply Finset.sum_congr rfl;intro k hk
     apply Finset.sum_congr rfl;intro l hl
     ring)
noncomputable def spectralSites (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ) : Fin n→Local :=
  fun i=>sourceR (u+ξ i)

theorem source_row_exchange (n : ℕ) (ξ : Fin n→ℝ) (u v : ℝ)
    (hu : ∀ i,YangBaxter.denominator (u+ξ i)≠0) (hv : ∀ i,YangBaxter.denominator (v+ξ i)≠0)
    (hd : YangBaxter.denominator (u-v)≠0) (s t : Space n) :
    sourceMatrix (u-v)*forward n (spectralSites n ξ u) (spectralSites n ξ v) s t=
      backward n (spectralSites n ξ u) (spectralSites n ξ v) s t*sourceMatrix (u-v) := by
  apply row_exchange
  intro i a b
  have hh : (u+ξ i)-(v+ξ i)=u-v := by ring
  simpa only [spectralSites,hh] using
    local_source_exchange (u+ξ i) (v+ξ i) (hu i) (hv i) (by simpa only [hh] using hd) a b
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix
lemma yangBaxter_denominator (u : ℝ) : YangBaxter.denominator u=Reflection.Q u :=
  Reflection.denominator_binding u
lemma yangBaxter_normalized (u : ℝ) : YangBaxter.sourceR u=Reflection.normalizedR u := by
  unfold YangBaxter.sourceR Reflection.normalizedR
  simp only [Transfer.a,Transfer.h,Transfer.v,Transfer.c,Transfer.d,Complex.ofReal_div]
  rfl
lemma yangBaxter_spectral (u : ℝ) (hu : Reflection.Q u≠0) :
    YangBaxter.sourceR u=Reflection.spectralR u := by
  rw [yangBaxter_normalized,Reflection.spectralR_normalized u hu]
lemma sourceMatrix_spectral (u : ℝ) (hu : Reflection.Q u≠0) :
    sourceMatrix u=Reflection.spectralR u := yangBaxter_spectral u hu
lemma spectralSites_exact (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ)
    (hu : ∀ i,Reflection.Q (u+ξ i)≠0) : spectralSites n ξ u=exactSites n ξ u := by
  funext i
  exact yangBaxter_spectral (u+ξ i) (hu i)

theorem exact_row_exchange (n : ℕ) (ξ : Fin n→ℝ) (u v : ℝ)
    (hu : ∀ i,Reflection.Q (u+ξ i)≠0) (hv : ∀ i,Reflection.Q (v+ξ i)≠0)
    (hd : Reflection.Q (u-v)≠0) (s t : Space n) :
    Reflection.spectralR (u-v)*forward n (exactSites n ξ u) (exactSites n ξ v) s t=
      backward n (exactSites n ξ u) (exactSites n ξ v) s t*Reflection.spectralR (u-v) := by
  have hh:=source_row_exchange n ξ u v
    (fun i=>by simpa only [yangBaxter_denominator] using hu i)
    (fun i=>by simpa only [yangBaxter_denominator] using hv i)
    (by simpa only [yangBaxter_denominator] using hd) s t
  simpa only [sourceMatrix_spectral (u-v) hd,spectralSites_exact n ξ u hu,
    spectralSites_exact n ξ v hv] using hh
end CriticalHoneycomb.Transfer.RowExchange

end

section

namespace CriticalHoneycomb.Transfer.Reflection
open Filter Topology
lemma continuous_sine : Continuous sine := by
  unfold sine
  fun_prop
lemma continuous_Q : Continuous Q := by
  unfold Q
  exact (continuous_sine.comp (continuous_const.add continuous_id)).mul
    (continuous_sine.comp (continuous_const.add continuous_id))
lemma continuous_bulkNumerator : Continuous bulkNumerator := by
  apply continuous_pi; intro p
  apply continuous_pi; intro q
  unfold bulkNumerator
  split <;> (try simp only [coeffA,coeffH,coeffV,coeffC,coeffD,Q,S,sine]) <;> fun_prop
lemma continuousAt_spectralR (u : ℝ) (hu : Q u≠0) : ContinuousAt spectralR u := by
  exact (continuous_Q.continuousAt.inv₀ hu).smul continuous_bulkNumerator.continuousAt
lemma continuousAt_boundary0 (t : ℝ) (ht : sine (gamma+t)≠0) :
    ContinuousAt boundary0 t := by
  apply continuousAt_pi.2; intro p
  apply continuousAt_pi.2; intro q
  unfold boundary0
  split_ifs
  · exact continuousAt_const
  · exact ((continuous_sine.comp (continuous_const.sub continuous_id)).continuousAt).div
      ((continuous_sine.comp (continuous_const.add continuous_id)).continuousAt) ht
  · exact continuousAt_const
lemma continuousAt_boundary1 (t : ℝ) (ht : sine (gamma+t)≠0) :
    ContinuousAt boundary1 t := by
  have h : ContinuousAt (fun u => sine (2*u)/sine (gamma+u)) t :=
    ((continuous_sine.comp (continuous_const.mul continuous_id)).continuousAt).div
      ((continuous_sine.comp (continuous_const.add continuous_id)).continuousAt) ht
  apply continuousAt_pi.2; intro p
  apply continuousAt_pi.2; intro q
  unfold boundary1
  split_ifs
  · exact h
  · exact continuousAt_const.mul h
  · exact continuousAt_const
lemma sine_zero_countable : Set.Countable {x : ℝ | sine x=0} := by
  apply (Set.countable_range (fun n : ℤ => (n:ℝ)*Real.pi)).mono
  intro x hx
  change sine x=0 at hx
  have hx' : Real.sin x=0 := by simpa only [sine,Complex.ofReal_eq_zero] using hx
  rcases Real.sin_eq_zero_iff.mp hx' with ⟨n,hn⟩
  exact ⟨n,hn⟩
lemma Q_zero_countable : Set.Countable {x : ℝ | Q x=0} := by
  have h₁ := sine_zero_countable.preimage (f:=fun x : ℝ => Real.pi/4+x)
    (fun x y h => add_left_cancel h)
  have h₂ := sine_zero_countable.preimage (f:=fun x : ℝ => b+x)
    (fun x y h => add_left_cancel h)
  change Set.Countable {x : ℝ | sine (Real.pi/4+x)=0} at h₁
  change Set.Countable {x : ℝ | sine (b+x)=0} at h₂
  simpa only [Q,mul_eq_zero,Set.ofPred_or] using h₁.union h₂

lemma dense_exchange_regular (u : ℝ) :
    Dense {v : ℝ | Q (u-v)≠0 ∧ Q (u+v)≠0 ∧ Q (-(u-v))≠0 ∧ Q (-(b-(u+v)))≠0} := by
  have h₁ := Q_zero_countable.preimage (f:=fun v : ℝ => u-v)
    (fun x y h => sub_right_injective h)
  have h₂ := Q_zero_countable.preimage (f:=fun v : ℝ => u+v)
    (fun x y h => add_left_cancel h)
  have h₃ := Q_zero_countable.preimage (f:=fun v : ℝ => -(u-v))
    (fun x y h => sub_right_injective (neg_injective h))
  have h₄ := Q_zero_countable.preimage (f:=fun v : ℝ => -(b-(u+v)))
    (fun x y h => add_left_cancel (sub_right_injective (neg_injective h)))
  have hd := (((h₁.union h₂).union h₃).union h₄).dense_compl ℝ
  convert hd using 1
  ext v
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_preimage,Set.mem_ofPred_eq]
  tauto
end CriticalHoneycomb.Transfer.Reflection

end

section

namespace CriticalHoneycomb.Transfer.RowExchange
open Reflection Filter Topology
lemma matrix_entry_continuousAt {a c k : Type*} [TopologicalSpace k]
    {f : ℝ → Matrix a c k} {u : ℝ} (h : ContinuousAt f u) (i : a) (j : c) :
    ContinuousAt (fun x => f x i j) u :=
  continuousAt_pi.1 (continuousAt_pi.1 h i) j
lemma continuousAt_row (n : ℕ) (A : ℝ → Fin n → Local) (u : ℝ)
    (hA : ∀ i, ContinuousAt (fun x => A x i) u) (s t : Space n) :
    ContinuousAt (fun x => row n (A x) s t) u := by
  induction n with
  | zero => exact continuousAt_const
  | succ n ih =>
    change ContinuousAt (fun x => block (A x 0) (s 0) (t 0) *
      row n (Fin.tail (A x)) (Fin.tail s) (Fin.tail t)) u
    have hb : ContinuousAt (fun x => block (A x 0) (s 0) (t 0)) u := by
      apply continuousAt_pi.2; intro i
      apply continuousAt_pi.2; intro j
      exact matrix_entry_continuousAt (hA 0) (i,s 0) (j,t 0)
    exact hb.mul (ih (fun x => Fin.tail (A x)) (fun i => hA i.succ) _ _)
lemma continuousAt_exact_row (n : ℕ) (ξ : Fin n → ℝ) (u : ℝ)
    (hu : ∀ i, Q (u+ξ i)≠0) (s t : Space n) :
    ContinuousAt (fun x => row n (exactSites n ξ x) s t) u := by
  apply continuousAt_row
  intro i
  exact (continuousAt_spectralR (u+ξ i) (hu i)).comp (f:=fun x : ℝ => x+ξ i)
    (continuousAt_id.add continuousAt_const)
end CriticalHoneycomb.Transfer.RowExchange
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet Filter Topology
open scoped Matrix BigOperators
lemma continuous_C : Continuous C := by
  exact TrivSqZeroExt.continuous_inl.comp TrivSqZeroExt.continuous_inl
lemma continuousAt_K (e : Jet) (u : ℝ) (hu : sine (gamma+u)≠0) (p : Pair) :
    ContinuousAt (fun x => K e x p) u := by
  have h0 : ContinuousAt (fun x => K0 x p) u :=
    continuousAt_const.mul (matrix_entry_continuousAt (continuousAt_boundary0 u hu) p.1 p.2.rev)
  have h1 : ContinuousAt (fun x => K1 x p) u :=
    continuousAt_const.mul (matrix_entry_continuousAt (continuousAt_boundary1 u hu) p.1 p.2.rev)
  exact (continuous_C.continuousAt.comp h0).add
    (continuousAt_const.mul (continuous_C.continuousAt.comp h1))
lemma continuousAt_bulkRows (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) (s t : Space N) :
    ContinuousAt (fun x => bulkRows N ξ x s t) u := by
  apply continuousAt_pi.2; intro p
  apply continuousAt_pi.2; intro q
  unfold bulkRows forward
  simp only [Matrix.sum_apply]
  apply tendsto_finsetSum
  intro v hv
  exact (matrix_entry_continuousAt (continuousAt_exact_row N ξ u (fun i => (hu.2.2 i).1) s v) p.1 q.1).mul
    (matrix_entry_continuousAt ((continuousAt_exact_row N ξ (b-u) (fun i => (hu.2.2 i).2) v t).comp (f:=fun x : ℝ => b-x)
      (continuousAt_const.sub continuousAt_id)) p.2 q.2)
lemma continuousAt_T (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) : ContinuousAt (T N ξ) u := by
  apply continuousAt_pi.2; intro s
  apply continuousAt_pi.2; intro t
  unfold T
  apply tendsto_finsetSum; intro p hp
  apply tendsto_finsetSum; intro q hq
  exact (((continuousAt_K eL (b-u) hu.2.1 p).comp (f:=fun x : ℝ => b-x)
    (continuousAt_const.sub continuousAt_id)).mul
    (continuous_C.continuousAt.comp (matrix_entry_continuousAt (continuousAt_bulkRows N ξ u hu s t) p q))).mul
    (continuousAt_K eR u hu.1 q)
lemma eventually_nonsingular (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) : ∀ᶠ x in 𝓝 u, Nonsingular N ξ x := by
  have h0 := ((continuous_sine.comp (continuous_const.add continuous_id)).continuousAt
    (x:=u)).eventually_ne hu.1
  have h1 := ((continuous_sine.comp (continuous_const.add
    (continuous_const.sub continuous_id))).continuousAt (x:=u)).eventually_ne hu.2.1
  have h2 : ∀ᶠ x in 𝓝 u, ∀ i, Q (x+ξ i)≠0 ∧ Q ((b-x)+ξ i)≠0 := by
    apply Filter.eventually_all.2
    intro i
    exact (((continuous_Q.comp (continuous_id.add continuous_const)).continuousAt
      (x:=u)).eventually_ne (hu.2.2 i).1).and
      (((continuous_Q.comp ((continuous_const.sub continuous_id).add continuous_const)).continuousAt
        (x:=u)).eventually_ne (hu.2.2 i).2)
  exact h0.and (h1.and h2)
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma K_tensor (e : Jet) (he : e*e=0) (t y : ℝ) :
    tensorBoundary (K e t) (K e y) =
      fun p => C (flatten4 (pairVector (boundary0 t) (boundary0 y)) p)+
        e*C (flatten4 (pairVector (boundary1 t) (boundary0 y)+
          pairVector (boundary0 t) (boundary1 y)) p) := by
  unfold K
  rw [square_zero_tensor C e he]
  rfl
lemma marked_right_invariant (e : Jet) (he : e*e=0) (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    (exactTrain t y).map C *ᵥ tensorBoundary (K e t) (K e y) =
      tensorBoundary (K e t) (K e y) := by
  rw [K_tensor e he]
  apply map_right_jet (k:=ℂ) (k':=Jet) (ι:=Aux Spin) C (exactTrain t y)
    (flatten4 (pairVector (boundary0 t) (boundary0 y)))
    (flatten4 (pairVector (boundary1 t) (boundary0 y)+pairVector (boundary0 t) (boundary1 y)))
    (exactTrain_right_constant t y hm hp hnm hnp ht hy)
    (exactTrain_right_linear t y hm hp hnm hnp ht hy) e
lemma marked_left_invariant (e : Jet) (he : e*e=0) (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (hnm : Q (-(t-y))≠0) (hnp : Q (-(b-(t+y)))≠0)
    (ht : sine (gamma+(b-t))≠0) (hy : sine (gamma+(b-y))≠0) :
    tensorBoundary (K e (b-t)) (K e (b-y)) ᵥ* (exactTrain t y).map C =
      tensorBoundary (K e (b-t)) (K e (b-y)) := by
  rw [K_tensor e he]
  apply map_left_jet (k:=ℂ) (k':=Jet) (ι:=Aux Spin) C (exactTrain t y)
    (flatten4 (pairVector (boundary0 (b-t)) (boundary0 (b-y))))
    (flatten4 (pairVector (boundary1 (b-t)) (boundary0 (b-y))+pairVector (boundary0 (b-t)) (boundary1 (b-y))))
    (exactTrain_left_constant t y hm hp hnm hnp ht hy)
    (exactTrain_left_linear t y hm hp hnm hnp ht hy) e
lemma JRow_exchange (N : ℕ) (ξ : Fin N→ℝ) (u v : ℝ)
    (hu : ∀ i, Q (u+ξ i)≠0) (hv : ∀ i, Q (v+ξ i)≠0)
    (hd : Q (u-v)≠0) :
    ∀ s t, (spectralR (u-v)).map C * forwardPair (JRow N ξ u) (JRow N ξ v) s t =
      backwardPair (JRow N ξ u) (JRow N ξ v) s t * (spectralR (u-v)).map C :=
by
  intro s t
  rw [forward_JRow,backward_JRow,←Matrix.map_mul,←Matrix.map_mul]
  exact congrArg (fun M : Matrix Pair Pair ℂ=>M.map C)
    (exact_row_exchange N ξ u v hu hv hd s t)
lemma exactTrain_jet (u v : ℝ) : (exactTrain u v).map C =
    auxTrain ((spectralR (b-(u+v))).map C) ((spectralR (u-v)).map C)
      ((spectralR (-(u-v))).map C) ((spectralR (-(b-(u+v)))).map C) := by
  unfold exactTrain
  exact map_auxTrain (k:=ℂ) (k':=Jet) (α:=Spin) C _ _ _ _

theorem closed_commutation_generic (N : ℕ) (ξ : Fin N→ℝ) (u v : ℝ)
    (hu : Nonsingular N ξ u) (hv : Nonsingular N ξ v)
    (hm : Q (u-v)≠0) (hp : Q (u+v)≠0)
    (hnm : Q (-(u-v))≠0) (hnp : Q (-(b-(u+v)))≠0) :
    Commute (T N ξ u) (T N ξ v) := by
  have h₁ : ∀ s t, (spectralR (b-(u+v))).map C *
      forwardPair (JRow N ξ (b-u)) (JRow N ξ v) s t =
      backwardPair (JRow N ξ (b-u)) (JRow N ξ v) s t *
        (spectralR (b-(u+v))).map C := by
    have hd : Q ((b-u)-v)≠0 := by
      rw [show (b-u)-v=b-(u+v) by ring,reflected_Q]
      exact hp
    simpa only [show (b-u)-v=b-(u+v) by ring] using
      JRow_exchange N ξ (b-u) v (fun i => (hu.2.2 i).2) (fun i => (hv.2.2 i).1) hd
  have h₂ := JRow_exchange N ξ u v (fun i => (hu.2.2 i).1) (fun i => (hv.2.2 i).1) hm
  have h₃ : ∀ s t, (spectralR (-(u-v))).map C *
      forwardPair (JRow N ξ (b-u)) (JRow N ξ (b-v)) s t =
      backwardPair (JRow N ξ (b-u)) (JRow N ξ (b-v)) s t *
        (spectralR (-(u-v))).map C := by
    have hd : Q ((b-u)-(b-v))≠0 := by simpa only [show (b-u)-(b-v)=-(u-v) by ring] using hnm
    simpa only [show (b-u)-(b-v)=-(u-v) by ring] using
      JRow_exchange N ξ (b-u) (b-v) (fun i => (hu.2.2 i).2) (fun i => (hv.2.2 i).2) hd
  have h₄ : ∀ s t, (spectralR (-(b-(u+v)))).map C *
      forwardPair (JRow N ξ u) (JRow N ξ (b-v)) s t =
      backwardPair (JRow N ξ u) (JRow N ξ (b-v)) s t *
        (spectralR (-(b-(u+v)))).map C := by
    have hd : Q (u-(b-v))≠0 := by simpa only [show u-(b-v)=-(b-(u+v)) by ring] using hnp
    simpa only [show u-(b-v)=-(b-(u+v)) by ring] using
      JRow_exchange N ξ u (b-v) (fun i => (hu.2.2 i).1) (fun i => (hv.2.2 i).2) hd
  have hl := marked_left_invariant eL (by simpa only [pow_two] using eL_sq) u v
    hm hp hnm hnp hu.2.1 hv.2.1
  have hr := marked_right_invariant eR (by simpa only [pow_two] using eR_sq) u v
    hm hp hnm hnp hu.1 hv.1
  rw [exactTrain_jet] at hl hr
  rw [T_closePair,T_closePair]
  exact closed_four_train (JRow N ξ u) (JRow N ξ (b-u))
    (JRow N ξ v) (JRow N ξ (b-v))
    ((spectralR (b-(u+v))).map C) ((spectralR (u-v)).map C)
    ((spectralR (-(u-v))).map C) ((spectralR (-(b-(u+v)))).map C)
    (K eL (b-u)) (K eL (b-v)) (K eR u) (K eR v) h₁ h₂ h₃ h₄ hl hr
open Filter Topology

theorem source_global_spectral_commutation : GlobalSpectralCommutation := by
  intro N ξ u v hu hv
  let D : Set ℝ := {w | Q (u-w)≠0 ∧ Q (u+w)≠0 ∧
    Q (-(u-w))≠0 ∧ Q (-(b-(u+w)))≠0}
  have hd : Dense D := dense_exchange_regular u
  have : Filter.NeBot (𝓝[D] v) := mem_closure_iff_nhdsWithin_neBot.mp (hd v)
  have hc := continuousAt_T N ξ v hv
  have hf : Tendsto (fun w => T N ξ u*T N ξ w) (𝓝[D] v)
      (𝓝 (T N ξ u*T N ξ v)) :=
    (continuousAt_const.mul hc).mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun w => T N ξ w*T N ξ u) (𝓝[D] v)
      (𝓝 (T N ξ v*T N ξ u)) :=
    (hc.mul continuousAt_const).mono_left nhdsWithin_le_nhds
  have he : (fun w => T N ξ u*T N ξ w) =ᶠ[𝓝[D] v]
      (fun w => T N ξ w*T N ξ u) := by
    have hmem : ∀ᶠ w in 𝓝[D] v, w∈D := self_mem_nhdsWithin
    have hreg := (eventually_nonsingular N ξ v hv).filter_mono (nhdsWithin_le_nhds (s:=D))
    filter_upwards [hmem,hreg] with w hw hns
    exact (closed_commutation_generic N ξ u w hu hns hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).eq
  exact tendsto_nhds_unique_of_eventuallyEq hf hg he
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet ClosedFourRow Filter Topology
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma spectral_PT_entry (u : ℝ) (p q : Pair) :
    spectralR u (q.2,q.1) p = spectralR u (p.2,p.1) q := by
  rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl
lemma spectral_PT_jet (u : ℝ) :
    ((spectralR u).map C)ᵀ*pairSwap=pairSwap*(spectralR u).map C := by
  funext p q
  rw [mul_pairSwap,pairSwap_mul]
  simp only [Matrix.transpose_apply,Matrix.map_apply,spectral_PT_entry]
lemma K_swap (e : Jet) (u : ℝ) (hd : Q (u-(b-u))≠0)
    (hu : sine (gamma+u)≠0) (hr : sine (gamma+(b-u))≠0) :
    (spectralR (u-(b-u))).map C*ᵥK e u = pairSwap*ᵥK e (b-u) := by
  have he : (spectralR (u-(b-u))).map C*ᵥK e u = fun p=>
      C ((spectralR (u-(b-u))*ᵥK0 u) p)+e*C ((spectralR (u-(b-u))*ᵥK1 u) p) := by
    funext p
    simp only [K,Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,map_mul,
      Finset.mul_sum,mul_add,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,source_K0_swap u hd hu hr,source_K1_swap u hd hu hr]
  funext p
  rw [pairSwap_mulVec]
  rfl
lemma spectral_reflection_generic (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) (hd : Q (u-(b-u))≠0) :
    T N ξ u = T N ξ (b-u) := by
  rw [T_closePair,T_closePair,sub_sub_cancel]
  funext s t
  rw [closePair_dot,closePair_dot]
  have he := JRow_exchange N ξ u (b-u) (fun i=>(hu.2.2 i).1)
    (fun i=>(hu.2.2 i).2) hd s t
  have hc := closed_pair_reflection ((spectralR (u-(b-u))).map C)
    (forwardPair (JRow N ξ u) (JRow N ξ (b-u)) s t)
    (backwardPair (JRow N ξ u) (JRow N ξ (b-u)) s t)
    (K eL (b-u)) (K eR u) (K eL u) (K eR (b-u))
    he (spectral_PT_jet (u-(b-u))) (K_swap eL u hd hu.1 hu.2.1)
    (K_swap eR u hd hu.1 hu.2.1)
  rw [swap_backward] at hc
  exact hc
lemma nonsingular_reflect (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) : Nonsingular N ξ (b-u) := by
  refine ⟨hu.2.1,?_,?_⟩
  · simpa only [sub_sub_cancel] using hu.1
  · intro i
    simpa only [sub_sub_cancel] using (hu.2.2 i).symm
lemma dense_swap_regular : Dense {u : ℝ|Q (u-(b-u))≠0} := by
  have h:=Q_zero_countable.preimage (f:=fun u : ℝ=>u-(b-u)) (fun x y h=>by linarith)
  exact h.dense_compl ℝ

theorem source_spectral_reflection (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ u) : T N ξ u=T N ξ (b-u) := by
  let D : Set ℝ := {x|Q (x-(b-x))≠0}
  have : Filter.NeBot (𝓝[D] u) := mem_closure_iff_nhdsWithin_neBot.mp (dense_swap_regular u)
  have hf := (continuousAt_T N ξ u hu).mono_left (nhdsWithin_le_nhds (s:=D))
  have hg := ((continuousAt_T N ξ (b-u) (nonsingular_reflect N ξ u hu)).comp
    (f:=fun x : ℝ=>b-x) (continuousAt_const.sub continuousAt_id)).mono_left
      (nhdsWithin_le_nhds (s:=D))
  have he : (fun x=>T N ξ x) =ᶠ[𝓝[D] u] (fun x=>T N ξ (b-x)) := by
    have hmem : ∀ᶠ x in 𝓝[D] u,x∈D := self_mem_nhdsWithin
    have hreg := (eventually_nonsingular N ξ u hu).filter_mono (nhdsWithin_le_nhds (s:=D))
    filter_upwards [hmem,hreg] with x hx hns
    exact spectral_reflection_generic N ξ x hns hx
  exact tendsto_nhds_unique_of_eventuallyEq hf hg he
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def parity (a : Spin) : ℂ := if a=1 then -1 else 1
lemma parity_sq (a : Spin) : parity a*parity a=1 := by
  unfold parity;split <;> ring
lemma sine_add_pi (u : ℝ) : sine (u+Real.pi) = -sine u := by
  simp [sine,Real.sin_add_pi]
lemma sine_sub_pi (u : ℝ) : sine (u-Real.pi) = -sine u := by
  simp [sine,Real.sin_sub_pi]
lemma Q_periodic (u : ℝ) : Q (u+Real.pi)=Q u := by
  simp [Q,←add_assoc,sine_add_pi]
lemma A_antiperiodic (u : ℝ) : coeffA (u+Real.pi)= -coeffA u := by
  simp [coeffA,show b-(u+Real.pi)=(b-u)-Real.pi by ring,sine_sub_pi]
lemma H_antiperiodic (u : ℝ) : coeffH (u+Real.pi)= -coeffH u := by
  simp [coeffH,sine_add_pi]
lemma V_periodic (u : ℝ) : coeffV (u+Real.pi)=coeffV u := by
  simp [coeffV,show b-(u+Real.pi)=(b-u)-Real.pi by ring,sine_sub_pi,sine_add_pi]
lemma C_periodic (u : ℝ) : coeffC (u+Real.pi)=coeffC u := by
  simp [coeffC,show b-(u+Real.pi)=(b-u)-Real.pi by ring,
    show Real.pi/4-(u+Real.pi)=(Real.pi/4-u)-Real.pi by ring,sine_sub_pi]
lemma D_periodic (u : ℝ) : coeffD (u+Real.pi)=coeffD u := by
  simp [coeffD,show u+Real.pi-L=(u-L)+Real.pi by ring,sine_add_pi]
lemma R_periodic_entry (u : ℝ) (p q : Pair) :
    spectralR (u+Real.pi) p q=parity p.1*parity q.1*spectralR u p q := by
  rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [spectralR,bulkNumerator,parity,Q_periodic,A_antiperiodic,H_antiperiodic,
      V_periodic,C_periodic,D_periodic,neg_div,mul_neg]
lemma boundary0_periodic (u : ℝ) (a b : Spin) : boundary0 (u+Real.pi) a b=boundary0 u a b := by
  simp [boundary0,show gamma-(u+Real.pi)=(gamma-u)-Real.pi by ring,
    ←add_assoc,sine_add_pi,sine_sub_pi]
lemma boundary1_antiperiodic (u : ℝ) (a b : Spin) : boundary1 (u+Real.pi) a b= -boundary1 u a b := by
  have hs : sine (2*(u+Real.pi))=sine (2*u) := by
    rw [show 2*(u+Real.pi)=(2*u+Real.pi)+Real.pi by ring,sine_add_pi,sine_add_pi,neg_neg]
  simp only [boundary1,hs,←add_assoc,sine_add_pi]
  split_ifs <;> simp [div_neg]
lemma K0_periodic_entry (u : ℝ) (p : Pair) :
    K0 (u+Real.pi) p=parity p.1*parity p.2*K0 u p := by
  simp only [K0,boundary0_periodic]
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp [parity,boundary0,Fin.rev]
lemma K1_periodic_entry (u : ℝ) (p : Pair) :
    K1 (u+Real.pi) p=parity p.1*parity p.2*K1 u p := by
  simp only [K1,boundary1_antiperiodic]
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp [parity,boundary1,Fin.rev]
lemma row_parity (n : ℕ) (A B : Fin n→Local)
    (h : ∀ i p q,B i p q=parity p.1*parity q.1*A i p q)
    (s t : Space n) (a b : Spin) :
    row n B s t a b=parity a*parity b*row n A s t a b := by
  induction n generalizing a b with
  | zero =>
    simp only [row,Matrix.one_apply]
    split_ifs with he
    · subst b;rw [parity_sq,mul_one]
    · ring
  | succ n ih =>
    simp only [row,Matrix.mul_apply,block,h,ih (Fin.tail A) (Fin.tail B) (fun i=>h i.succ)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    calc
      _=(parity a*parity b*(A 0 (a,s 0) (c,t 0)*
        row n (Fin.tail A) (Fin.tail s) (Fin.tail t) c b))*(parity c*parity c) := by ring
      _=_ := by rw [parity_sq,mul_one]
lemma spectral_row_periodic (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (s t : Space N) (a b : Spin) :
    row N (exactSites N ξ (u+Real.pi)) s t a b=
      parity a*parity b*row N (exactSites N ξ u) s t a b := by
  apply row_parity
  intro i p q
  simp only [exactSites,show u+Real.pi+ξ i=(u+ξ i)+Real.pi by ring,R_periodic_entry]
lemma spectral_row_sub_period (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (s t : Space N) (a b : Spin) :
    row N (exactSites N ξ (u-Real.pi)) s t a b=
      parity a*parity b*row N (exactSites N ξ u) s t a b := by
  have h:=spectral_row_periodic N ξ (u-Real.pi) s t a b
  rw [sub_add_cancel] at h
  rw [h]
  symm
  calc
    _=(parity a*parity a)*(parity b*parity b)*row N (exactSites N ξ (u-Real.pi)) s t a b := by ring
    _=_ := by rw [parity_sq,parity_sq];ring
noncomputable def pairParity (p : Pair) : ℂ := parity p.1*parity p.2
lemma pairParity_sq (p : Pair) : pairParity p*pairParity p=1 := by
  unfold pairParity
  calc
    _=(parity p.1*parity p.1)*(parity p.2*parity p.2) := by ring
    _=1 := by rw [parity_sq,parity_sq,mul_one]
lemma bulkRows_periodic (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (s t : Space N) (p q : Pair) :
    bulkRows N ξ (u+Real.pi) s t p q=
      pairParity p*pairParity q*bulkRows N ξ u s t p q := by
  simp only [bulkRows,forward,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.of_apply,show b-(u+Real.pi)=(b-u)-Real.pi by ring,
    spectral_row_periodic,spectral_row_sub_period,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  unfold pairParity
  ring
lemma Kpart_periodic (i : Bool) (u : ℝ) (p : Pair) :
    (if i then K1 (u+Real.pi) p else K0 (u+Real.pi) p)=
      pairParity p*(if i then K1 u p else K0 u p) := by
  cases i <;> simp [pairParity,K0_periodic_entry,K1_periodic_entry]
lemma Kpart_sub_period (i : Bool) (u : ℝ) (p : Pair) :
    (if i then K1 (u-Real.pi) p else K0 (u-Real.pi) p)=
      pairParity p*(if i then K1 u p else K0 u p) := by
  have h:=Kpart_periodic i (u-Real.pi) p
  rw [sub_add_cancel] at h
  rw [h,←mul_assoc,pairParity_sq,one_mul]
lemma coefficient_periodic (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (i j : Bool) :
    coefficient N ξ (u+Real.pi) i j=coefficient N ξ u i j := by
  funext s t
  simp only [coefficient,show b-(u+Real.pi)=(b-u)-Real.pi by ring,
    Kpart_sub_period,Kpart_periodic,bulkRows_periodic]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  calc
    _=(pairParity p*pairParity p)*(pairParity q*pairParity q)*
      ((if i then K1 (b-u) p else K0 (b-u) p)*bulkRows N ξ u s t p q*
      (if j then K1 u q else K0 u q)) := by ring
    _=_ := by rw [pairParity_sq,pairParity_sq,one_mul,one_mul]

theorem source_spectral_periodicity (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) :
    T N ξ (u+Real.pi)=T N ξ u := by
  funext s t
  simp only [T_coefficients,coefficient_periodic]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def cap (p : Pair) : ℂ := if p.2=p.1.rev then Reflection.phase^(spinValue p.1) else 0
lemma sum_cap (f : Pair→ℂ) : (∑ p,f p*cap p)=∑ a : Spin,f (a,a.rev)*Reflection.phase^(spinValue a) := by
  rw [Fintype.sum_prod_type]
  simp [cap,mul_ite]
lemma localForward_cap_expand (A B : Local) (s t : Spin) (p : Pair) :
    (localForward A B s t*ᵥcap) p=
      ∑ v : Spin,∑ a : Spin,A (p.1,s) (a,v)*B (p.2,v) (a.rev,t)*Reflection.phase^(spinValue a) := by
  simp only [localForward,Matrix.sum_mulVec,Finset.sum_apply]
  apply Finset.sum_congr rfl;intro v hv
  rw [Matrix.mulVec,dotProduct,sum_cap]
  rfl
lemma phase_cancel (a c : Spin) :
    Reflection.phase^(spinValue a.rev-spinValue c)*Reflection.phase^(spinValue a)=Reflection.phase^(-spinValue c) := by
  have hp : Reflection.phase≠0 := point_ne_zero (Real.pi/4)
  rw [←zpow_add₀ hp,spinValue_rev]
  congr 1
  omega
lemma localForward_cap (u : ℝ) (hu : Q u≠0) (hn : Q (-u)≠0) (s t : Spin) :
    localForward (spectralR u) (spectralR (b+u)) s t*ᵥcap=
      if s=t then cap else 0 := by
  funext p
  rw [localForward_cap_expand]
  have hcross (v a : Spin) :
      spectralR (b+u) (p.2,v) (a.rev,t)*Reflection.phase^(spinValue a)=
        Reflection.phase^(-spinValue p.2)*spectralR (-u) (p.2.rev,t) (a,v) := by
    rw [show b+u=b-(-u) by ring,source_crossing,Fin.rev_rev]
    calc
      _=(Reflection.phase^(spinValue a.rev-spinValue p.2)*Reflection.phase^(spinValue a))*
          spectralR (-u) (p.2.rev,t) (a,v) := by ring
      _=_ := by rw [phase_cancel]
  have he : (∑ v : Spin,∑ a : Spin,spectralR u (p.1,s) (a,v)*
      spectralR (b+u) (p.2,v) (a.rev,t)*Reflection.phase^(spinValue a))=
      Reflection.phase^(-spinValue p.2)*((spectralR u*(spectralR (-u))ᵀ) (p.1,s) (p.2.rev,t)) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro v hv
    apply Finset.sum_congr rfl;intro a ha
    rw [mul_assoc,hcross]
    ring
  rw [he,spectral_unitarity u hu hn,Matrix.one_apply]
  by_cases hs : s=t
  · subst t
    by_cases hp : p.2=p.1.rev
    · have hp' : p.2.rev=p.1 := by rw [hp,Fin.rev_rev]
      simp [hp,cap,spinValue_rev]
    · have hp' : p.1≠p.2.rev := by intro h;apply hp;rw [h,Fin.rev_rev]
      simp [hp',cap,hp]
  · simp [hs]
lemma localForward_period_cap (u : ℝ) (hu : Q u≠0) (hn : Q (-u)≠0) (s t : Spin) :
    localForward (spectralR (u+Real.pi)) (spectralR (b+u)) s t*ᵥ(fun p=>parity p.1*cap p)=
      if s=t then (fun p=>parity p.1*cap p) else 0 := by
  funext p
  have hl (q : Pair) :
      localForward (spectralR (u+Real.pi)) (spectralR (b+u)) s t p q=
      parity p.1*parity q.1*localForward (spectralR u) (spectralR (b+u)) s t p q := by
    simp only [localForward,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,block,R_periodic_entry,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro v hv;ring
  change (∑ q,localForward (spectralR (u+Real.pi)) (spectralR (b+u)) s t p q*
    (parity q.1*cap q))=_
  simp only [hl]
  have he : (∑ q,parity p.1*parity q.1*localForward (spectralR u) (spectralR (b+u)) s t p q*
      (parity q.1*cap q))=parity p.1*(localForward (spectralR u) (spectralR (b+u)) s t*ᵥcap) p := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro q hq
    have hq:=parity_sq q.1
    linear_combination parity p.1*localForward (spectralR u) (spectralR (b+u)) s t p q*cap q*hq
  rw [he,localForward_cap u hu hn]
  split_ifs <;> simp
end CriticalHoneycomb.Transfer.SpectralFamily

end

end OAI
