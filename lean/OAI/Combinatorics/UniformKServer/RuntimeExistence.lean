import Mathlib
import OAI.Combinatorics.UniformKServer.RuntimeCertificate

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite
open scoped Classical

def time (u r a : ℕ) : ℕ := Classical.choose (LiteralBound.exists_time u r a)
theorem time_good (u r a : ℕ) : LiteralBound.finishes (time u r a) u r a=true :=
  Classical.choose_spec (LiteralBound.exists_time u r a)

def needA (u r a : ℕ) : ℕ := max
  (chosen (unpack u) (requestToken r) a).bits.length (time u (requestToken r) a)
def needR (b u r : ℕ) : ℕ := max ((natCode (r+1)).length+1)
  ((Finset.range (2^(b+1))).sup (needA u r))
def needU (n b u : ℕ) : ℕ := max (u.bits.length+1) ((Finset.range n).sup (needR b u))
def bound (n b : ℕ) (S : List ℕ) : ℕ := max (b+1) (S.toFinset.sup (needU n b))

theorem exists_cert {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) :
    ∃c,verify n k v c=true := by
  obtain ⟨S,h₀,hS⟩:=finite_closed hk hkn v hR hT
  let b:=B k v
  let T:=bound n b S
  refine ⟨(S,T),(verify_iff _ _ _ _).mpr ⟨h₀,le_max_left _ _,?_⟩⟩
  intro u hu
  have hU : needU n b u≤T :=
    (Finset.le_sup (f:=needU n b) (List.mem_toFinset.mpr hu)).trans (le_max_right _ _)
  refine ⟨(le_max_left _ _).trans hU,?_⟩
  intro r hr
  have hR' : needR b u r≤T :=
    (Finset.le_sup (f:=needR b u) (Finset.mem_range.mpr hr)).trans
      ((le_max_right _ _).trans hU)
  refine ⟨(le_max_left _ _).trans hR',?_⟩
  intro a ha
  have hA : needA u r a≤T :=
    (Finset.le_sup (f:=needA u r) (Finset.mem_range.mpr ha)).trans
      ((le_max_right _ _).trans hR')
  exact ⟨(hS u hu r hr a).1,(hS u hu r hr a).2,(le_max_left _ _).trans hA,
    LiteralBound.monotone_time (time_good _ _ _) ((le_max_right _ _).trans hA)⟩

end UniformKServer.RuntimeCertificate

end

end OAI
