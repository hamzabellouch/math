import OAI.Computability.DepthThree.TapeHashRow

namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashOuter

open TapeMultiProgram TapeUnary TapeRegister

abbrev State := TapeForLoop.State TapeHashRow.State

def program : TapeMultiProgram State :=
  TapeForLoop.program indexC ringDegree TapeHashRow.program TapeHashRow.start

def start : State := TapeForLoop.start
def done : State := TapeForLoop.done

def progressStore (σ : TapeStore) (i : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits
    (hashUpdateRows (σ keyBits) (σ dataBits) (List.range i) (σ hashBits)))
    indexC (List.replicate i true)

theorem progress_zero (σ : TapeStore) (hc : σ indexC = []) :
    progressStore σ 0 = σ := by
  simp only [progressStore, List.range_zero, hashUpdateRows_nil,
    Function.update_eq_self, List.replicate_zero, ← hc]

theorem progress_step (σ : TapeStore) (i d : ℕ) (hd : (σ dataBits).length = d) :
    TapeHashRow.resultStore (progressStore σ i) i d =
      Function.update (progressStore σ (i + 1)) indexC (List.replicate i true) := by
  funext q
  by_cases hc : q = indexC
  · subst q
    simp [TapeHashRow.resultStore, progressStore, indexC, hashBits]
  · by_cases hh : q = hashBits
    · subst q
      simp [TapeHashRow.resultStore, progressStore, hashUpdateRows_range_succ, hd,
        indexC, hashBits, keyBits, dataBits]
    · simp [TapeHashRow.resultStore, progressStore, hc, hh]

theorem row_cost_le (i d r : ℕ) (hi : i ≤ r) :
    d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 ≤
      64 * (d + r + 1) ^ 2 := by
  have hm := Nat.mul_le_mul_left d
    (show 4 * i + 8 * d + 29 ≤ 4 * r + 8 * d + 29 by omega)
  have hfirst : d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 ≤
      d * (4 * r + 8 * d + 29) + 4 * r + 8 * d + 25 := by omega
  apply hfirst.trans
  nlinarith [Nat.zero_le (d * r)]

theorem runs_outer (σ : TapeStore) (d r : ℕ)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (progressStore σ r)))
      (r * (64 * (d + r + 1) ^ 2 + 4 * r + 12) + (4 * r + 8)) := by
  let τ : ℕ → TapeTapes := fun i => storeTapes (progressStore σ i)
  have hindex : ∀ i ≤ r, τ i indexC = counterTape i := by
    intro i hi
    simp [τ, progressStore, counterTape]
  have hbound : ∀ i ≤ r, τ i ringDegree = counterTape r := by
    intro i hi
    simp [τ, progressStore, counterTape, hr, ringDegree, indexC, hashBits]
  have hbody : ∀ i < r, RunsIn TapeHashRow.program.step
      (cfg TapeHashRow.start (τ i))
      (cfg TapeHashRow.done (Function.update (τ (i + 1)) indexC (counterTape i)))
      (64 * (d + r + 1) ^ 2) := by
    intro i hi
    have hs := TapeHashRow.runs_row (progressStore σ i) i d r hi
      (by simp [progressStore, hd, dataLength, indexC, hashBits])
      (by simp [progressStore, ha, indexA, indexC, hashBits])
      (by simp [progressStore, hb, indexB, indexC, hashBits])
      (by simp [progressStore])
      (by simpa [progressStore, keyBits, indexC, hashBits] using hkey)
      (by simpa [progressStore, dataBits, indexC, hashBits] using hdata)
      (by simp [progressStore, hout, indexC, hashBits])
    have hs' := hs.mono (row_cost_le i d r hi.le)
    simpa only [τ, progress_step σ i d hdata, storeTapes_update, counterTape] using hs'
  have hall := TapeForLoop.runs_zero (by decide : indexC ≠ ringDegree)
    TapeHashRow.program TapeHashRow.start TapeHashRow.done τ r (64 * (d + r + 1) ^ 2)
    hindex hbound hbody TapeHashRow.program_done
  simpa only [program, start, done, τ, progress_zero σ hc] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashOuter
end DepthThreeLowerBound

end OAI
