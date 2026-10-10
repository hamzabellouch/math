import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.NumAbs

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
open BinaryRational
noncomputable def ofWords {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (decode (f x))) := by
  have hh := hf.comp BinaryRational.normalize_computes
  simpa only [Function.comp_def] using hh
noncomputable def nat {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (value (f x):ℚ)) := by
  have hh := hf.comp BinaryRational.natWords_computes
  simpa only [Function.comp_def,BinaryRational.natWords,BinaryRational.castIntWords_encode,Int.cast_natCast] using hh
noncomputable def const (r : ℚ) : PolyComputes (fun _ : List Bool=>encode r) := const_computes (encode r)
noncomputable def add {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x+g x)) := by
  have hh := (hf.pair hg).comp addWords_computes
  simpa only [Function.comp_def,addWords_pair] using hh
noncomputable def mul {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x*g x)) := by
  have hh := (hf.pair hg).comp mulWords_computes
  simpa only [Function.comp_def,mulWords_pair] using hh
noncomputable def sub {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x-g x)) := by
  have hh := (hf.pair hg).comp subWords_computes
  simpa only [Function.comp_def,subWords_pair] using hh
noncomputable def div {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x/g x)) := by
  have hh := (hf.pair hg).comp divWords_computes
  simpa only [Function.comp_def,divWords_pair] using hh
noncomputable def inv {f : List Bool → ℚ} (hf : PolyComputes (fun x=>encode (f x))) :
    PolyComputes (fun x=>encode ((f x)⁻¹)) := by
  have hh := hf.comp invWords_computes
  simpa only [Function.comp_def,invWords_encode] using hh
noncomputable def neg {f : List Bool → ℚ} (hf : PolyComputes (fun x=>encode (f x))) :
    PolyComputes (fun x=>encode (-f x)) := by
  have hh := hf.comp negWords_computes
  simpa only [Function.comp_def,negWords_encode] using hh
noncomputable def floor {f : List Bool → ℚ} (hf : PolyComputes (fun x=>encode (f x))) :
    PolyComputes (fun x=>encode ((⌊f x⌋:ℤ):ℚ)) := by
  have hi : PolyComputes (fun x=>Signed.encode (⌊f x⌋:ℤ)) := by
    have hh := hf.comp floorWords_computes
    simpa only [Function.comp_def,floorWords_encode] using hh
  have hh := hi.comp castIntWords_computes
  simpa only [Function.comp_def,castIntWords_encode] using hh
noncomputable def root {f : List Bool → ℚ} {d : List Bool → ℕ}
    (hf : PolyComputes (fun x=>encode (f x))) (hd : PolyComputes (fun x=>(d x).bits)) :
    PolyComputes (fun x=>encode (Ellipsoid.rationalRootUpper (d x) (f x))) := by
  have hh := (hf.pair hd).comp BinaryEllipsoidRoot.run_computes
  simpa only [Function.comp_def,BinaryEllipsoidRoot.run_encode] using hh
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
