import OAI.MathematicalPhysics.Heisenberg.PeriodicLeakage

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix

end

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q q : ℕ} [NeZero m] [NeZero Q]

def phaseHom (h : Q∣m) : Fin m →+ Fin Q where
  toFun j := (j.val : Fin Q)
  map_zero' := by simp
  map_add' i j := by
    apply Fin.ext
    simp only [Fin.val_natCast,Fin.val_add]
    rw [Nat.mod_mod_of_dvd _ h,Nat.add_mod]

lemma phaseHom_sub (h : Q∣m) (a b : Fin m) :
    ((a-b).val%Q)=((phaseHom h a-phaseHom h b).val) := by
  have hh:=congrArg Fin.val ((phaseHom h).map_sub a b)
  exact hh

def reverseIndex (q : ℕ) : Equiv.Perm (Fin m) where
  toFun j := (q:Fin m)-j
  invFun j := (q:Fin m)-j
  left_inv j := sub_sub_cancel _ j
  right_inv j := sub_sub_cancel _ j

lemma reverseIndex_next (j : Fin m) :
    (finRotate m).symm (reverseIndex q j)=reverseIndex q (finRotate m j) := by
  apply (finRotate m).injective
  simp only [Equiv.apply_symm_apply,finRotate_apply,reverseIndex,Equiv.coe_fn_mk]
  simp only [sub_add_eq_sub_sub,sub_add_cancel]

lemma reverseIndex_prev (hq : 0 < q) (j : Fin m) :
    (finRotate m).symm (reverseIndex q j)=((q-1:ℕ):Fin m)-j := by
  apply (finRotate m).injective
  simp only [Equiv.apply_symm_apply,finRotate_apply,reverseIndex,Equiv.coe_fn_mk]
  have h : ((q-1:ℕ):Fin m)+1=(q:Fin m) := by
    calc
      _ = ((q-1+1:ℕ):Fin m) := by simp only [Nat.cast_add,Nat.cast_one]
      _ = (q:Fin m) := by rw [Nat.sub_add_cancel hq]
  rw [sub_add_eq_add_sub,h]

lemma reverse_phase_spatial (hdiv : Q∣m) (hq : 0 < q) (hqQ : q ≤ Q)
    (j : Fin m) (hj : j.val%Q < q) :
    ((finRotate m).symm (reverseIndex q j)).val%Q=q-1-j.val%Q := by
  rw [reverseIndex_prev hq,phaseHom_sub hdiv]
  have hQm : Q ≤ m := Nat.le_of_dvd (NeZero.pos m) hdiv
  have hqm : q-1 < m := by omega
  have hqQ' : q-1 < Q := by omega
  have ha : phaseHom hdiv ((q-1:ℕ):Fin m)=((q-1:ℕ):Fin Q) := by
    simp [phaseHom,Fin.val_natCast,Nat.mod_eq_of_lt hqm]
  rw [ha,Fin.sub_val_of_le]
  · simp only [Fin.val_natCast,Nat.mod_eq_of_lt hqQ',phaseHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  · change j.val%Q ≤ (q-1)%Q
    rw [Nat.mod_eq_of_lt hqQ']
    omega

lemma reverse_phase_completion (hdiv : Q∣m) (hq : 0 < q) (hqQ : q ≤ Q)
    (j : Fin m) (hj : q ≤ j.val%Q) :
    q ≤ ((finRotate m).symm (reverseIndex q j)).val%Q := by
  rw [reverseIndex_prev hq,phaseHom_sub hdiv]
  have hQm : Q ≤ m := Nat.le_of_dvd (NeZero.pos m) hdiv
  have hqm : q-1 < m := by omega
  have hqQ' : q-1 < Q := by omega
  have ha : phaseHom hdiv ((q-1:ℕ):Fin m)=((q-1:ℕ):Fin Q) := by
    simp [phaseHom,Fin.val_natCast,Nat.mod_eq_of_lt hqm]
  rw [ha]
  have hh:=Fin.intCast_val_sub_eq_sub_add_ite ((q-1:ℕ):Fin Q) (phaseHom hdiv j)
  have hn : ¬phaseHom hdiv j ≤ ((q-1:ℕ):Fin Q) := by
    change ¬j.val%Q ≤ (q-1)%Q
    rw [Nat.mod_eq_of_lt hqQ']
    omega
  rw [ite_eq_right hn] at hh
  simp only [Fin.val_natCast,Nat.mod_eq_of_lt hqQ',phaseHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk] at hh
  change q ≤ (((q-1:ℕ):Fin Q)-(j.val:Fin Q)).val
  have hmod:=Nat.mod_lt j.val (NeZero.pos Q)
  omega

end Heisenberg.Schedule

end

noncomputable section
open scoped Classical BigOperators
open Matrix
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma prefix_cons (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K (n+1)=prefixMatrix (fun j=>K (j+1)) n*K 0 := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    rw [prefixMatrix,ih,prefixMatrix,Matrix.mul_assoc]

lemma prefix_congr (K L : ℕ → Matrix V V ℝ) (n : ℕ)
    (h : ∀ j,j < n → K j=L j) : prefixMatrix K n=prefixMatrix L n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixMatrix,prefixMatrix,h n (by omega),ih (fun j hj=>h j (by omega))]

lemma prefix_reverse (K : ℕ → Matrix V V ℝ) (n a : ℕ) :
    (prefixMatrix (fun j=>(K (a+n-1-j)).transpose) n).transpose=
      prefixMatrix (fun j=>K (a+j)) n := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    rw [prefix_cons,Matrix.transpose_mul,Matrix.transpose_transpose]
    have he : prefixMatrix (fun j=>(K (a+(n+1)-1-(j+1))).transpose) n=
        prefixMatrix (fun j=>(K (a+n-1-j)).transpose) n := by
      apply prefix_congr
      intro j hj
      congr 2
      omega
    rw [he,ih,prefixMatrix]
    congr 1

omit [DecidableEq V] in
lemma squareNorm_toLp (f : EuclideanSpace ℝ V) : squareNorm f.ofLp=‖f‖^2 := by
  simpa only [squareNorm,Real.norm_eq_abs,sq_abs] using (EuclideanSpace.norm_sq_eq f).symm

lemma energy_two_prefixes (K : ℕ → Matrix V V ℝ) (N u v : ℕ) (huv : u+v ≤ N)
    (hK : ∀ j,j < N → DoublySubstochastic (K j)) (f : EuclideanSpace ℝ V) :
    ((‖f‖^2-‖euclideanMap (prefixMatrix K u) f‖^2)+
      (‖f‖^2-‖euclideanMap (prefixMatrix (fun j=>(K (N-1-j)).transpose) v) f‖^2))/2 ≤
      Heisenberg.Hitting.energy (prefixMatrix K N) f.ofLp := by
  let A:=prefixMatrix K u
  let M:=prefixMatrix (fun j=>K (u+j)) (N-v-u)
  let B:=prefixMatrix (fun j=>K (N-v+j)) v
  have hM : DoublySubstochastic M := prefix_substochastic _ _ (fun j hj=>hK _ (by omega))
  have he : prefixMatrix K N=B*M*A := by
    have hN : N=(u+(N-v-u))+v := by omega
    conv_lhs => rw [hN,prefix_add,prefix_add]
    change prefixMatrix (fun j=>K (u+(N-v-u)+j)) v*(M*A)=B*M*A
    have hu : u+(N-v-u)=N-v := by omega
    rw [hu,Matrix.mul_assoc]
  have hB : B.transpose=prefixMatrix (fun j=>(K (N-1-j)).transpose) v := by
    have hh:=prefix_reverse K v (N-v)
    have hNv : N-v+v=N := by omega
    rw [hNv] at hh
    exact (congrArg Matrix.transpose hh).symm.trans (Matrix.transpose_transpose _)
  have hh:=two_ends A M B hM f.ofLp
  rw [←he,hB] at hh
  change (_+_)/2 ≤ _ at hh
  have heE : Heisenberg.Hitting.energy (prefixMatrix K N) f.ofLp=
      squareNorm f.ofLp-dot f.ofLp ((prefixMatrix K N)*ᵥ f.ofLp) := by
    simp [Heisenberg.Hitting.energy,squareNorm,dot,Matrix.mulVec,dotProduct,mul_sub,
      Finset.sum_sub_distrib,Finset.mul_sum,pow_two]
  rw [heE]
  convert hh using 1
  simp only [←squareNorm_toLp,A]
  rfl

end Heisenberg.MeshPair

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Schedule
variable {m : ℕ} [NeZero m]

lemma reverse_run (q : ℕ) (t : Fin m) (j : ℕ) :
    reverseIndex q (run (reverseIndex q t) j)=t-(j:Fin m) := by
  simp only [reverseIndex,Equiv.coe_fn_mk,run]
  rw [sub_add_eq_sub_sub,sub_sub_cancel]

lemma reverse_predecessor (q : ℕ) (t : Fin m) (j : ℕ) (hj : j < m) :
    (finRotate m).symm (reverseIndex q (run (reverseIndex q t) j))=run t (m-1-j) := by
  rw [reverse_run,finRotate_symm_apply]
  have he : (m-1-j)+j+1=m := by omega
  have hh : ((m-1-j:ℕ):Fin m)+(j:Fin m)+1=0 := by
    calc
      _ = ((m-1-j+j+1:ℕ):Fin m) := by simp only [Nat.cast_add,Nat.cast_one]
      _ = 0 := by rw [he]; simp
  apply add_right_cancel (b:=(j:Fin m)+1)
  change (t-(j:Fin m)-1)+((j:Fin m)+1)=(t+((m-1-j:ℕ):Fin m))+((j:Fin m)+1)
  rw [←sub_add_eq_sub_sub,sub_add_cancel,add_assoc,←add_assoc _ (j:Fin m),hh,add_zero]

end Heisenberg.Schedule

namespace Heisenberg.Exposure
open Heisenberg.Schedule Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma layerSum_reverse (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V)) (p : T → ℝ)
    (F : (T → Bool) → ℝ) :
    (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) c*F (c ∘ s))=
      ∑ c,layerMass s a b P p c*F c := by
  let e : (T → Bool) ≃ (T → Bool) := Equiv.arrowCongr s (Equiv.refl Bool)
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  change layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (c ∘ s.symm)*F ((c ∘ s.symm) ∘ s)=_
  rw [layerMass_reverse]
  congr 2
  funext i
  simp

omit [Fintype T] in
lemma reversed_period_sweep {m : ℕ} [NeZero m] (q : ℕ)
    (a b : Fin m → V) (P : Set (Fin m×V)) (p : Fin m → ℝ)
    (base : Fin m → Bool) (I : Set V) (t : Fin m) (v : ℕ) (hv : v ≤ m)
    (f : EuclideanSpace ℝ V) :
    exposedSweep (finRotate m).symm (a ∘ (finRotate m).symm) (b ∘ (finRotate m).symm)
      (base ∘ (finRotate m).symm) P I (p ∘ (finRotate m).symm)
      (fun j=>reverseIndex q (run (reverseIndex q t) j)) v f=
    euclideanMap (prefixMatrix
      (fun j=>(exposedStep (finRotate m) a b base P I p (run t (m-1-j))).transpose) v) f := by
  rw [exposedSweep_prefix]
  apply congrArg (fun K=>euclideanMap K f)
  apply prefix_congr
  intro j hj
  rw [exposedStep_reverse,reverse_predecessor q t j (lt_of_lt_of_le hj hv)]

end Heisenberg.Exposure

end
end

noncomputable section
open scoped Classical Topology
open Set Filter Metric
namespace Heisenberg.Pin

lemma nonzero_uniform_limit_disk {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hF : ∀ᶠ i in φ, DiffContOnCl ℂ (F i) (ball c r))
    (h₀ : ∀ᶠ i in φ, ∀ z ∈ closedBall c r, F i z ≠ 0)
    (hf : TendstoUniformlyOn F f φ (closedBall c r))
    (hbound : ∀ z ∈ sphere c r, ε ≤ ‖f z‖) : f c ≠ 0 := by
  have hevent : ∀ᶠ i in φ, ε / 2 ≤ ‖F i c‖ := by
    filter_upwards [hF, h₀, (Metric.tendstoUniformlyOn_iff.mp hf) (ε / 2)
      (half_pos hε)] with i hi hz hclose
    have hfront : ∀ z ∈ frontier (ball c r), ‖(F i z)⁻¹‖ ≤ (ε / 2)⁻¹ := by
      intro z hz'
      rw [frontier_ball c hr.ne'] at hz'
      have hcz := hclose z (sphere_subset_closedBall hz')
      have hlen : ε / 2 ≤ ‖F i z‖ := by
        have htriangle := norm_sub_norm_le (f z) (F i z)
        rw [dist_eq_norm] at hcz
        linarith [hbound z hz']
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (half_pos hε) hlen) (half_pos hε)).mpr hlen
    have hb : ‖(F i c)⁻¹‖ ≤ (ε / 2)⁻¹ := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hi.inv (by simpa [closure_ball c hr.ne'] using hz)) hfront
      rw [closure_ball c hr.ne']
      exact mem_closedBall_self hr.le
    rw [norm_inv] at hb
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hz c (mem_closedBall_self hr.le)))
      (half_pos hε)).mp hb
  have hlim := (hf.tendsto_at (mem_closedBall_self hr.le)).norm
  have hlen : ε / 2 ≤ ‖f c‖ := ge_of_tendsto hlim hevent
  intro hz
  simp only [hz, norm_zero] at hlen
  exact (not_le_of_gt (half_pos hε)) hlen

lemma polynomial_disk {p : Polynomial ℂ} (hp : p ≠ 0) {U : Set ℂ} (hU : IsOpen U)
    {c : ℂ} (hc : c ∈ U) :
    ∃ r > 0, closedBall c r ⊆ U ∧ ∀ z ∈ sphere c r, p.eval z ≠ 0 := by
  let Z : Set ℂ := {z | p.IsRoot z} \ {c}
  have hZ : IsClosed Z := ((Polynomial.finite_setOfPred_isRoot hp).sdiff).isClosed
  have hcZ : c ∈ Zᶜ := by simp [Z]
  have hn : U ∩ Zᶜ ∈ 𝓝 c := (hU.inter hZ.isOpen_compl).mem_nhds ⟨hc, hcZ⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · exact fun z hz => (hδU (closedBall_subset_ball (half_lt_self hδ) hz)).1
  · intro z hz hzero
    have hmem := (hδU (closedBall_subset_ball (half_lt_self hδ)
      (sphere_subset_closedBall hz))).2
    apply hmem
    refine ⟨hzero, ?_⟩
    simp only [mem_singleton_iff]
    intro heq
    subst z
    have hs : dist c c = δ / 2 := hz
    rw [dist_self] at hs
    exact (half_pos hδ).ne' hs.symm

theorem polynomial_nonvanishing_limit {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ i in φ, DifferentiableOn ℂ (F i) U)
    (h₀ : ∀ᶠ i in φ, ∀ z ∈ U, F i z ≠ 0)
    (hf : TendstoLocallyUniformlyOn F (fun z => p.eval z) φ U) :
    ∀ c ∈ U, p.eval c ≠ 0 := by
  intro c hc
  obtain ⟨r, hr, hball, hsphere⟩ := polynomial_disk hp hU hc
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (p.continuous.norm.continuousOn)
  refine nonzero_uniform_limit_disk (F := F) (φ := φ) (f := fun z => p.eval z) (c := c) (r := r) hr (norm_pos_iff.mpr (hsphere z₀ hz₀)) ?_ ?_ ?_ ?_
  · filter_upwards [hF] with i hi
    apply DifferentiableOn.diffContOnCl
    exact hi.mono (by simpa only [closure_ball c hr.ne'] using hball)
  · filter_upwards [h₀] with i hi z hz
    exact hi z (hball hz)
  · exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf
      (closedBall c r) hball (isCompact_closedBall c r)
  · exact fun z hz => hmin hz

end Heisenberg.Pin
end
end

end OAI
