import Mathlib
import OAI.Combinatorics.UniformKServer.TierLifetimes
import OAI.Combinatorics.UniformKServer.TierKeys

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierKeyProcess
open FiniteProbability Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def key (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Option (Fin N) :=
  TierKeys.key (Real.log (1+(K:ℝ)^2)) r ((TierLifetimes.live r K q c t τ).sort (·≤·)) c ω p

theorem conditional_separation (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (τ : TierLifetimes.Tape N) (x y : X) (hxy : dist x y<r/4) :
    (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(K:ℝ)^2)) r)).expect
      (fun ω => if key r K q c t τ ω x≠key r K q c t τ ω y then (1:ℝ) else 0)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hv := (TierLifetimes.valid r K hK hq q c t).1 τ
  apply TierKeys.separation (TierSchedule.run r K q c t) _ c K hK r hr x y hxy
  · exact sort_nodup _ _
  · intro i hi
    exact (mem_filter.mp (hv ((mem_sort _).mp hi))).1
  · intro i hi
    exact (mem_filter.mp (hv ((mem_sort _).mp hi))).2

theorem separation (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (x y : X) (hxy : dist x y<r/4) :
    ((TierLifetimes.law (N:=N) K hq).prod
      (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(K:ℝ)^2)) r))).expect
      (fun z => if key r K q c t z.1 z.2 x≠key r K q c t z.1 z.2 y then (1:ℝ) else 0)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  rw [Law.expect_prod _ _ (fun τ ω => if key r K q c t τ ω x≠key r K q c t τ ω y then (1:ℝ) else 0)]
  have hh := (TierLifetimes.law (N:=N) K hq).expect_mono _
    (fun _ => 2*Real.log (1+(K:ℝ)^2)*dist x y/r)
    (fun τ => conditional_separation r hr K hK hq q c t τ x y hxy)
  simpa only [Law.expect_const] using hh

omit [Fintype X] in
theorem covers (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (i : Fin N) (hi : key r K q c t τ ω p=some i) : dist p (c i)≤2*r := by
  have hc := TierKeys.key_covers _ _ _ c ω p i hi
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hd := TierRadius.cover_outer _ r hr (ω i) (c i) p hc
  simpa only [dist_comm] using hd.le

omit [Fintype X] in
theorem coverage (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K) (q : Fin N → Prop) (c : Fin N → X)
    (n : Fin N) (hn : q n) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) :
    (key r K q c (n.val+1) τ ω (c n)).isSome=true := by
  obtain ⟨i,hi,hd⟩ := TierLifetimes.coverage r hr.le K (by omega) q c n hn τ
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hcover : (ω i).val (c i,c n)=true := TierRadius.cover_inner _ r hlam hr (ω i) _ _
    (by rw [dist_comm]; linarith)
  change (List.find? (fun j => (ω j).val (c j,c n))
    ((TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·))).isSome = true
  rw [List.isSome_find?]
  exact List.any_eq_true.mpr ⟨i,(mem_sort _).mpr hi,hcover⟩

end UniformKServer.TierKeyProcess

end


end

end OAI
