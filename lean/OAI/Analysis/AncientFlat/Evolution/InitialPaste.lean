import OAI.Analysis.AncientFlat.Evolution.TimePaste
import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff Laplacian
namespace ParabolicInitial
open ParabolicInterior ClassicalIBP
variable {V : Type} {E : Type*}
def initialJoin (u v : ℝ → V → E) (t : ℝ) (x : V) : E :=
  if t<0 then v (max (-1/2) t) x else u t x
lemma initialJoin_pos (u v : ℝ → V → E) {t : ℝ} (ht : 0≤t) :
    initialJoin u v t=u t := by funext x; simp [initialJoin,not_lt_of_ge ht]
lemma initialJoin_neg (u v : ℝ → V → E) {t : ℝ} (ht : t<0) (ht' : -1/2≤t) :
    initialJoin u v t=v t := by funext x; simp [initialJoin,ht,max_eq_right ht']
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma initialJoin_contDiff (u v : ℝ → V → E)
    (hu : ∀ t, ContDiff ℝ 4 (u t))
    (hv : ∀ t∈Icc (-1/2:ℝ) 0, ContDiff ℝ 4 (v t)) (t : ℝ) :
    ContDiff ℝ 4 (initialJoin u v t) := by
  by_cases ht : t<0
  · have he : initialJoin u v t=v (max (-1/2) t) := by funext x; simp [initialJoin,ht]
    rw [he]
    exact hv _ ⟨le_max_left _ _,max_le (by norm_num) ht.le⟩
  · rw [initialJoin_pos u v (le_of_not_gt ht)]; exact hu t
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma initialJoin_hasDerivAt (h : ℝ) (hh : 0<h) (u ut v vt : ℝ → V → E)
    (x : V) (hu : ∀ t∈Icc 0 h, HasDerivWithinAt (fun s => u s x) (ut t x) (Icc 0 h) t)
    (hv : ∀ t∈Icc (-1/2:ℝ) 0, HasDerivWithinAt (fun s => v s x) (vt t x) (Icc (-1/2:ℝ) 0) t)
    (h0 : v 0 x=u 0 x) (ht0 : vt 0 x=ut 0 x)
    (t : ℝ) (ht : t∈Ioo (-1/4:ℝ) h) :
    HasDerivAt (fun s => initialJoin u v s x) (initialJoin ut vt t x) t := by
  have he (s : ℝ) (hs : s∈Icc (-1/2:ℝ) 0) : initialJoin u v s x=v s x := by
    rcases lt_or_eq_of_le hs.2 with h | h
    · rw [initialJoin_neg u v h hs.1]
    · subst s; rw [initialJoin_pos u v le_rfl]; exact h0.symm
  by_cases hn : t<0
  · have H := (hv t ⟨by linarith [ht.1],hn.le⟩).hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) hn)
    rw [initialJoin_neg ut vt hn (by linarith [ht.1])]
    exact H.congr_of_eventuallyEq (mem_of_superset (Icc_mem_nhds (by linarith [ht.1] : (-1/2:ℝ)<t) hn) he)
  by_cases hp : 0<t
  · have H := (hu t ⟨hp.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds hp ht.2)
    rw [initialJoin_pos ut vt hp.le]
    apply H.congr_of_eventuallyEq
    filter_upwards [Ici_mem_nhds hp] with s hs
    rw [initialJoin_pos u v hs]
  have hz : t=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
  subst t
  rw [initialJoin_pos ut vt le_rfl]
  have Hleft := (hv 0 ⟨by norm_num,le_rfl⟩).congr_of_mem he (by norm_num)
  rw [ht0] at Hleft
  have Hright := (hu 0 ⟨le_rfl,hh.le⟩).congr_of_mem
    (fun s hs => congrFun (initialJoin_pos u v hs.1) x) (by simp [hh.le])
  have HL := Hleft.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by norm_num : (-1/2:ℝ)<0))
  have HR := Hright.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hh)
  have hi : Iic (0:ℝ)∪Ici 0=univ := by ext s; simp
  simpa only [hi,hasDerivWithinAt_univ] using HL.union HR
lemma initial_jet_zero (u : V → E) (hu : ∀ x, ‖x‖<2 → u x=0) (n : ℕ)
    (x : V) (hx : ‖x‖<2) : iteratedFDeriv ℝ n u x=0 := by
  have he : u=ᶠ[𝓝 x] (fun _ => (0:E)) := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
    exact hu y hy
  have H := (he.iteratedFDeriv ℝ n).eq_of_nhds
  rw [H]
  simp
lemma initialJoin_jet (u v : ℝ → V → E) (n : ℕ) (p : V × ℝ) (hp : -1/2≤p.2) :
    iteratedFDeriv ℝ n (initialJoin u v p.2) p.1=
      timeJoin (fun p => iteratedFDeriv ℝ n (v p.2) p.1)
        (fun p => iteratedFDeriv ℝ n (u p.2) p.1) p := by
  by_cases ht : p.2<0
  · rw [initialJoin_neg u v ht hp]; simp [timeJoin,ht]
  · rw [initialJoin_pos u v (le_of_not_gt ht)]; simp [timeJoin,ht]
lemma initialJoin_holder_jet (α h M N : ℝ) (hα : 0≤α) (hh : 0≤h) (hM : 0≤M) (hN : 0≤N)
    (u ut v vt : ℝ → V → ℂ)
    (hu : JetBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc 0 h} u ut M)
    (hv : JetBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) 0} v vt N)
    (h0 : ∀ n, n≤4 → ∀ x, ‖x‖<3/2 → iteratedFDeriv ℝ n (v 0) x=iteratedFDeriv ℝ n (u 0) x)
    (ht0 : ∀ x, ‖x‖<3/2 → vt 0 x=ut 0 x) :
    JetBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) h}
      (initialJoin u v) (initialJoin ut vt) (2*(M+N)) := by
  have hMN : 0≤M+N := add_nonneg hM hN
  constructor
  · intro n hn
    have H := holder_timeJoin α (M+N) (-1/2) h hα hMN (by norm_num) hh
      {x : V | ‖x‖<3/2} _ _ ((hv.1 n hn).mono (by linarith))
      ((hu.1 n hn).mono (by linarith)) (h0 n hn)
    constructor
    · intro p hp
      simpa only [initialJoin_jet u v n p hp.2.1] using H.1 p hp
    · intro p hp q hq
      simpa only [initialJoin_jet u v n p hp.2.1,
        initialJoin_jet u v n q hq.2.1] using H.2 p hp q hq
  · have H := holder_timeJoin α (M+N) (-1/2) h hα hMN (by norm_num) hh
      {x : V | ‖x‖<3/2} _ _ (hv.2.mono (by linarith)) (hu.2.mono (by linarith)) ht0
    have he (p : V × ℝ) (hp : ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) h) :
        initialJoin ut vt p.2 p.1=timeJoin (fun p => vt p.2 p.1) (fun p => ut p.2 p.1) p := by
      by_cases ht : p.2<0
      · rw [initialJoin_neg ut vt ht hp.2.1]; simp [timeJoin,ht]
      · rw [initialJoin_pos ut vt (le_of_not_gt ht)]; simp [timeJoin,ht]
    exact ⟨fun p hp => by simpa only [he p hp] using H.1 p hp,
      fun p hp q hq => by simpa only [he p hp,he q hq] using H.2 p hp q hq⟩
end ParabolicInitial

end

end OAI
