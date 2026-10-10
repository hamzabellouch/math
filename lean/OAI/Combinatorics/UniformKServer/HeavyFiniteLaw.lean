import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyBirths
import OAI.Combinatorics.UniformKServer.HeavySeparation

namespace OAI

                                     
section

/-! The exact finite uniform-radius law for the literal heavy process. The
slot pool is fixed before the horizon; only the independent tape is truncated
at the finite horizon under analysis. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords FiniteProbability
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance finDecEq (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def radiusStream (r : ℝ) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) (t : ℕ) : ℝ :=
  if h : t<N then HeavyRadius.radius r (ω ⟨t,h⟩) else 16*r

omit [Fintype X] in
theorem radiusStream_bounds (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r)
    (t : ℕ) : radiusStream r N ω t ∈ Set.Icc (16*r) (20*r) := by
  unfold radiusStream
  split_ifs
  · exact HeavyRadius.radius_bounds r hr _
  · constructor <;> linarith

def endpoint (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) : State X Λ r :=
  run a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) N

theorem endpoint_centers (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) :
    centers (endpoint a hr hΛ h x N ω)=HeavySchedule.centers r h x N :=
  run_centers _ _ _ _ _ _ _ _

def birthFin (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (hN : 0<N) (c : X) : Fin N :=
  if hc : births r h x N c<N then ⟨births r h x N c,hc⟩ else ⟨0,hN⟩

theorem endpoint_radius (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (hN : 0<N) (ω : Fin N → HeavyRadius.Sample (X:=X) r)
    (l : Λ) (hl : l ∈ (endpoint a hr hΛ h x N ω).present) :
    (endpoint a hr hΛ h x N ω).radius l=HeavyRadius.radius r
      (ω (birthFin (r:=r) h x N hN ((endpoint a hr hΛ h x N ω).center l))) := by
  have hb := run_birth a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) N l hl
  change births r h x N ((endpoint a hr hΛ h x N ω).center l)<N ∧ _ at hb
  rw [show (endpoint a hr hΛ h x N ω).radius l=radiusStream r N ω
    (births r h x N ((endpoint a hr hΛ h x N ω).center l)) from hb.2]
  simp only [radiusStream,birthFin,dite_eq_left hb.1]

theorem endpoint_separation (a : X) (hr : 0 < r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (y z : X) :
    (Law.pi (fun _ : Fin N => HeavyRadius.law (X:=X) r)).expect
      (fun ω => if key (endpoint a hr.le hΛ h x N ω) y ≠ key (endpoint a hr.le hΛ h x N ω) z then (1:ℝ) else 0)
      ≤ dist y z/r := by
  by_cases hN : 0<N
  · exact static_separation hr (HeavySchedule.centers r h x N) (HeavySchedule.centers_separated r h x N)
      (birthFin (r:=r) h x N hN) (endpoint a hr.le hΛ h x N)
      (endpoint_centers a hr.le hΛ h x N) (endpoint_radius a hr.le hΛ h x N hN) y z
  · have hzero : N=0 := by omega
    subst N
    have he (ω : Fin 0 → HeavyRadius.Sample (X:=X) r) (p : X) :
        key (endpoint a hr.le hΛ h x 0 ω) p=none := by
      apply (key_none _ p).mpr
      simp only [endpoint,run,runPair,empty,covers,notMem_empty,false_and,exists_false,not_false_eq_true]
    simp only [he,ne_eq,not_true_eq_false,ite_false,Law.expect_const]
    positivity

theorem heavy_close_key (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : h t) (y : X) (hd : dist y (x t) ≤ 8*r) :
    key (run a hr hΛ h x R hR (t+1)) y=key (run a hr hΛ h x R hR (t+1)) (x t) := by
  have hc := HeavySchedule.centers_coverage r hr h x t hh
  rw [←run_centers a hr hΛ h x R hR] at hc
  obtain ⟨c,hc,hcx⟩ := hc
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
  let S := run a hr hΛ h x R hR (t+1)
  have hcovx : covers S l (x t) := by
    refine ⟨hl,?_⟩
    have hb := (S.radius_bounds l hl).1
    rw [dist_comm] at hcx
    linarith
  have hcovy : covers S l y := by
    refine ⟨hl,?_⟩
    have hb := (S.radius_bounds l hl).1
    have ht := dist_triangle (S.center l) (x t) y
    rw [dist_comm (S.center l) (x t),dist_comm (x t) y] at ht
    linarith
  exact ((key_some S hr y l).mpr hcovy).trans ((key_some S hr (x t) l).mpr hcovx).symm

end UniformKServer.HeavyProcess

end


end

end OAI
